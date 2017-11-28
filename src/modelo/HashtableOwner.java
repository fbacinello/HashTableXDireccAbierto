package modelo;

import java.util.AbstractCollection;
import java.util.AbstractSet;
import java.util.Collection;
import java.util.Collections;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

/**
 *
 * @author Franco Bacinello
 * @param <K>
 * @param <V>
 */
public class HashtableOwner< K, V > implements Map< K, V >
{
    //private K key;
    //private V value;

    class Casilla < K, V > {

        private int state;
        private K key;
        private V value;

        public Casilla (int state, K key, V value) {
            this.state = state;
            this.key = key;
            this.value = value;
        }

        public V getValue() {
            return value;
        }

        public void setValue(V value) {
            this.value = value;
        }

        public int getState() {
            return state;
        }

        public void setState(int state) {
            this.state = state;
        }

        public K getKey() {
            return key;
        }

        public void setKey(K key) {
            this.key = key;
        }

        @Override
        public String toString() {
            return key + "=" + value;
        }
    }
    
    private Casilla< K, V >[] items;

    private float loadFactor;

    private static int STATE_OPEN = 1;
    private static int STATE_OCUPADO = 2;
    private static int STATE_TUMBA = 3;
    
    private static final int KEYS = 0;
    private static final int VALUES = 1;
    private static final int CASILLA = 2;

    /**
     * Constructor de la Clase. Construye una nueva tabla hash vacío con una
     * capacidad inicial predeterminada (11) y con un factor de carga de 0.75.
     */
    public HashtableOwner() {

        items = new Casilla[11];
        this.loadFactor = 0.75f;

        init();
    }

    /**
     * Constructor de la Clase. Construye una nueva tabla hash vacío con una
     * capacidad inicial especificada y el factor de carga por defecto,
     * que es 0,75.
     * Si la capacidad espeficada es menor a 11, entonces se crea la tabla hash
     * con tamaño igual a 11. De ser mayor a 11 se procede a verificar que el mismo
     * sea un número primo, de no ser asi se calcula el numero primo cercada mayor a el.
     * Ésto es así para evitar el agrupamiento secundario.
     * @param initialCapacity es el tamaño que tendra el tabla inicialmente
     * simpre y cuando sea mayor que 11 y sea un numero primo, en caso contrario
     * se procede a calcularlo.
     */
    public HashtableOwner(int initialCapacity) {

        if (initialCapacity < 11) {
            items = new Casilla[11];
        }
        else {
            if (isPrimo(initialCapacity)) items = new Casilla[initialCapacity];
            else items = new Casilla[nextPrimo(initialCapacity)];
        }

        this.loadFactor = 0.75f;
        init();
    }

    /**
     * Constructor de la Clase. Construye una nueva tabla hash vacío con una
     * capacidad inicial y factor de carga especificados.
     * @param initialCapacity es el tamaño que tendra el tabla inicialmente
     * simpre y cuando sea mayor que 11 y sea un numero primo, en caso contrario
     * se procede a calcularlo.
     * @param loadFactor factor de carga de la hash table. Debe ser menor o igual
     * a 1. Cualquier otro valor superior a 1 se tomará el valor por defecto (0.75).
     */
    public HashtableOwner(int initialCapacity, float loadFactor) {

        if (initialCapacity < 11) {
            items = new Casilla[11];
        }
        else {
            if (isPrimo(initialCapacity)) items = new Casilla[initialCapacity];
            else items = new Casilla[nextPrimo(initialCapacity)];
        }

        this.loadFactor = ( loadFactor < 1f ) ? loadFactor : 0.75f;
        
        init();
    }

    /**
     * Constructor de la Clase. Construye un nuevo tabla hash con las mismas
     * asignaciones que el mapa dado. La tabla hash se crea con una capacidad
     * inicial suficiente para mantener las asignaciones en el mapa dado y un
     * factor de carga por defecto, que es de 0.75.
     * @param t el mapa cuya asignaciones son para ser colocado en este mapa.
     * Lanza: NullPointerException - si el mapa especificado es nulo.
     */
    public HashtableOwner(Map<? extends K, ? extends V> t) {
        try {

            int capacity = t.size();

            if (capacity < 11) {
                items = new Casilla[11];
            }
            else {
                if (isPrimo(capacity)) items = new Casilla[capacity];
                else items = new Casilla[nextPrimo(capacity)];
            }

            this.loadFactor = 0.75f;
            putAll(t);

        } catch (NullPointerException exp) {
            throw new NullPointerException(exp.getMessage());
        }
    }

    /**
     * Calcula y retorna el numero de elementos almacenados en la Hashtable.
     * @return el numero de claves en la hashtable
     */
    public int size() {

        int c = 0;

        for (int i = 0; i < items.length; i++) {
            Casilla casilla = items[i];
            if (casilla.state == STATE_OCUPADO) c++;
        }
        return c;
    }

    /**
     * Comprueba si la hash table se encuentra vacia. De ser asi retorna un true,
     * caso contrario, un false.
     * @return
     */
    public boolean isEmpty() {
        
        for (Casilla<K, V> item : items) {
            Casilla casilla = item;
            if (casilla.state == STATE_OCUPADO) {
                return false;
            }
        }
        return true;
    }

    /**
     * Inserta un objeto con la clave especificada como parámetro.
     * Ni la clave ni el valor puede ser nulos.
     * El objeto se inserta siguiendo las reglas de la agrupacion secundaria
     * (resolviendo el problema de la agrupacion primaria).
     * @param key - clave de la tabla hash
     * @param value - objeto a insertar
     * @return el objeto anterior de la clave especificada en la tabla hash, o
     * nulo si no tiene uno.
     */
    public V put(K key, V value) {
        /*
         * Si la clave o valor son nulos entonces lanzar una Exception.
         */
        if (value == null || key == null)
            throw new NullPointerException();

        /*
         * Si el porcentaje de ocupacion excede al factor de carga entonces se
         procede a realizar un reHash.
         */
        if ( proportionOccupation() > loadFactor ) rehash();

        int indice = hashCode(key);
        int j = 1;
        int aux = indice;

        /*
         * Si la casilla i en donde queremos entrar tiene estado 2 (ocupada)
         y la clave que tiene es distinta a la que vamos a insertar
         entonces seguimos a la i+(j^1), i+(j^2), ..., i+(j^n) con j = 1,2,..,n
         hasta encontrar una desocupada.
         * Nota: si la clave ya se encuentra en la table entonces sobrescribimos su valor
         */
        while (items[aux].getState() == STATE_OCUPADO &&
                !( items[aux].getKey().equals(key) )) {
            aux = indice + (j*j);
            j++;

            if ( aux >= items.length )
                aux = 0;
            //aux = aux % items.length;
        }

        /*
        Sobreescribimos.
        */
        items[aux].setState(STATE_OCUPADO);
        items[aux].setKey(key);
        items[aux].setValue(value);

        /*
         * Retornamos el objeto que se encuentra en al anterior indice del objeto
         * nuevo insertado. Caso de no a ver ninguno devuelve null.
         */
        return items[aux - 1].getValue();
    }

    /**
     *
     */
    public void clear() {
        init();
    }
    
    public boolean contains(Object value)
    {
        return containsValue(value);
    }
    
    /**
     * Crea una copia superficial de esta tabla hash. Toda la estructura de la 
     * propia tabla hash se copia, pero las claves y los valores no se clonan. 
     * Esta es una operación relativamente cara.
     * @return un clon de la HashTable.
     * @throws java.lang.CloneNotSupportedException
     */
    @Override
    public Object clone() throws CloneNotSupportedException
    {
        try {
            HashtableOwner<K, V> ht = (HashtableOwner<K, V>) super.clone();
        
            //ht.items = new Casilla[items.length];
            
            return ht;
        } catch (CloneNotSupportedException ex) {
            throw new InternalError();
        }       
    }

    /**
     * Comprueba si la clave pasada como parametro se encuentra en la hashtable
     * @param key - clave a buscar.
     * @return true - si la clave existe en la hash table, caso contrario retorna
     * false.
     * @throws NullPointerException - si la clave es nula.
     */
    public boolean containsKey(Object key) {
        /*
         * Si la clave es nula lanzar excepcion.
         */
        if ( key == null ) throw new NullPointerException();

        /*
         * Si no hay elementos en la hash table retornar null.
         */
        if ( size() ==  0 ) return false;
        
        int indice = hashCode(key);
        
        boolean b = false;

        while ( !b ) {
            if (!( items[indice].getKey().equals(key)))
                indice++;
            else {
                b = true;
                break;
            }

           /*
            * Si nos pasamos, volvemos al principio del arreglo.
            */
           if(indice >= items.length)
               indice = 0;
        }
        return b;
    }

    /**
     * Comprueba si el valor pasado como parametro se encuentra en la hashtable
     * @param value - valor a buscar.
     * @return true - si el valor se encuentra en la hash table, caso contrario retorna
     * false.
     * @throws NullPointerException - si el valor es nula.
     */
    public boolean containsValue(Object value) {
        /*
         * Si la clave es nula lanzar excepcion.
         */
        if ( value == null ) throw new NullPointerException();

        /*
         * Si no hay elementos en la hash table retornar null.
         */
        if ( size() ==  0 ) return false;
        
        for (Casilla<K, V> item : items) {
            Casilla casilla = item;
            if (casilla.getValue() != null && casilla.getValue().equals((K)value))
                return true;
        }
        return false;
    }
    
    /**
     * Compara el objeto especificado con este mapa
     * @param o
     * @return true si el objeto Object especificado es igual a este mapa
     */
    @Override
    public boolean equals(Object o)
    {
        return (o == this);
    }
    
    public Enumeration<V> elements()
    {
       return this.<V>getEnumeration(VALUES);  
    }
    
    public Enumeration<K> keys()
    {
        return this.<K>getEnumeration(KEYS);
    }

    /**
     * Retorna el valor para la clave especificada como parametro que esta
     * mapeada en la base de datos.
     * La idea esta basada en la busqueda de orden directo 0(1).
     * Si la insercion se hace con agrupacion secundaria, entonces la busqueda
     * se hara de la misma forma.
     * @param key - clave para hallar su valor.
     * @return el valor correspondiente a la clave pasada como parametro. 
     * Y null en caso de no existir dicha clave.
     * @throws: NullPointerException - Si la clave es null
     */
    public V get(Object key) {
        /*
         * Si la clave es null entonces lanzar una Exception.
         */
        if (key == null)
            throw new NullPointerException();

        int indice = hashCode(key);
        int j = 1;
        int aux = indice;

        /*
         * Si la casilla i en donde queremos buscar tiene estado 2 (ocupada)
         y la clave que buscamos es distinta a la que el indice te llevo
         entonces seguimos a la i+(j^1), i+(j^2), ..., i+(j^n) con j = 1,2,..,n
         hasta encontrar la clave deseada.
         */
        while ( items[aux].getState() == STATE_OCUPADO &&
                !( items[aux].getKey().equals(key) ) ) {
            aux = indice + (j*j);
            j++;

            if ( aux > items.length )
                aux = 0;
        }

        /*
         * Retornamos el objeto con la clave indicada.
         */
        return items[aux].getValue();
    }

    /**
     * Elimina la clave (y su valor correspondiente) de esta tabla hash.
     * Este método no hace nada si la clave no está en la tabla hash.
     * @param key - clave que debe ser eliminada
     * @return el valor al que la clave había sido asignada en esta tabla hash,
     * o null si la llave no tiene una asignación.
     * @throws NullPointerException - Si la clave es nula.
     */
    public V remove(Object key) {
        /*
         * Si la clave es nula lanzar excepcion.
         */
        if ( key == null ) throw new NullPointerException();

        /*
         * Si no hay elementos en la hash table retornar null.
         */
        if ( size() ==  0 ) return null;

        int indice = hashCode(key);
        
        boolean b = false;

        while ( !b ) {
            if (!( items[indice].getKey().equals(key)))
                indice++;
            else {
                b = true;
                break;
            }

           /*
            * Si nos pasamos, volvemos al principio del arreglo.
            */
           if(indice > items.length)
               indice = 0;
       }

       /*
        * Si b es igual a true -> Encontramos el objeto a borrar.
        */
       if ( b ) {
           V temp = items[indice].getValue(); //Recuperamos el objeto
           items[indice].setState(STATE_TUMBA);
           items[indice].setKey(null);
           items[indice].setValue(null);
           return temp;
       }
       return null;
    }

    /**
     *
     * @param m
     */
    public void putAll(Map<? extends K, ? extends V> m) {
        Iterator it = m.entrySet().iterator();
        
        while (it.hasNext()) {
            Map.Entry< K, V > e = (Map.Entry)it.next();
            put(e.getKey(), e.getValue());
        }
    }

    public Set<K> keySet() {
        Set<K> s = new HashSet<K>(items.length, loadFactor);
        
        for (int i = 0; i < items.length; i++) {
            s.add(items[i].getKey());
        }
        return s;
    }

    public Collection<V> values() {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    public Set<Entry<K, V>> entrySet() {
        
        Map.Entry<K, V> m = new Entry<K, V>() {

            public K getKey() {
                throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
            }

            public V getValue() {
                throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
            }

            public V setValue(V value) {
                throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
            }
        };
        
        Set<Entry<K, V>> set = new AbstractSet<Entry<K, V>>() {

            @Override
            public Iterator<Entry<K, V>> iterator() {
                throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
            }

            @Override
            public int size() {
                throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
            }
        };
        return set;
    }

    /**
     * Redimensiona la colleccion en un 50% mas y agrupa por agrupacion secundaria.
     */
    protected void rehash(){
        /*
         Creamos un tabla temporal con tamaño mayor al 50 % que el tabla anterior
         y con numero primero siguiente.
         */
        Casilla[] temp = new Casilla[nextPrimo((int)(items.length * 1.5))];
        int j=1;
        int aux;

        /*
         * Inicializamos la nueva tabla...
         */
        for ( int i=0; i<temp.length; i++ )
            temp[i] = new Casilla(STATE_OPEN, null, null);

        /*
         * Re Hashing
         */
        for ( int i=0; i<items.length; i++ ) {
            Casilla casilla = items[i];
            if ( casilla.getValue() != null ) {
                /*
                HashCode.
                */
                int indice = casilla.getKey().hashCode() % temp.length;
                
                aux = indice;

                while ( temp[aux].getState() == STATE_OCUPADO ) {
                    aux = indice + (j*j);
                    j++;

                    if ( aux > temp.length )
                        aux = 0;
                }

                temp[aux].setState(STATE_OCUPADO);
                temp[aux].setKey(casilla.getKey());
                temp[aux].setValue(casilla.getValue());
            }
        }
        /*
        Cambiamos la referencia hacia el nuevo tabla
        */
        items = temp;
    }

    /**
    * Este metodo verica que dado un n° cualquiera comprueva de que sea un numero primo.
    * @param n es el numero a verificar que sea primo.
    * @return devuelve true si es primo o false en caso contrario.
    */
    private boolean isPrimo(int n) {
        int count = 0;
        boolean b = true;

        for (int i = 1; i <= n; i++) {
            if ( (n % i) == 0 ) count++;
        }

        /*
         * Si se tiene mas de 2 divisiones entonces no corresponde a un numero primo.
         */
        if (count > 2) b = false;

        return b;
    }

    /**
    * Este metodo calcula el proximo n° primo seguido de un numero pasado como
     * parametro.
    * @param n es numero al cual queremos obtener su siguiente numero primo.
    * @return devulve dicho numero primo posterior.
    */
    private int nextPrimo(int n) {
        n++;

        while( !isPrimo(n) )  {
            n++;
        }

        /*
         * Al salir ya habremos encontrado el siguiente nº primo y lo devolvemos.
         */
        return n;
    }

    /**
    * Función hash. Toma el hashCode() de un objeto, y retorna un índice para 
    * entrar en el arreglo items.
    * @param k es el objetor en el cual le extraeremos el valor hashCode.
    * @return el índice para entrar en la tabla items.
    */
    public int hashCode(Object k){
        int m = items.length;
        int hc = k.hashCode();
        return hc % m;
    }

    /**
     * Método Helper de los constructores que inicia todas las casilla de la
     * hashtable con estado = 1 e info = null.
     */
    private void init() {
        /*
         * Iniciamos el vector con estado 1 (abierto) y cn null todas las casillas.
         */
        for (int i= 0; i < items.length; i++) {
            items[i] = new Casilla(STATE_OPEN, null, null);
        }
    }

    /**
    * Calcula el porcentaje de ocupacion que posee el tabla.
    * @return el porcentaje de ocupacion.
    */
    private float proportionOccupation() {
      int count = 0;
        for (Casilla<K, V> item : items) {
            Casilla casilla = item;
            if ( casilla.getState() == STATE_OCUPADO ) count++;
        }
      return count/items.length;
    }

    /**
     * Obtiene y devuelve una cadena con todos los elementos de la Hash Table.
     * @return la cadena con todos los elementos que hay.
     */
    @Override
    public String toString() {
        String cadena = "No hay elementos en la Hash Table ...";
        
        boolean b = false;
        
        for (Casilla<K, V> item : items) {
            Casilla casilla = item;
            if (casilla.getState() == STATE_OCUPADO) {
                if (!b) {
                    b = true;
                    cadena = "";
                }
                cadena += casilla.toString() + ", ";
            }
        }
        return cadena;
    }
    
    private <T>Enumeration<T> getEnumeration(int type) {
        if (isEmpty()) {
            return Collections.emptyEnumeration();
        } else {
            return new Enumerator(type);
        }
    }
    
    private class Enumerator<T> implements Enumeration<T>
    {
        int index = 0;
        int type;
        
        
        Enumerator(int type){
            this.type = type;
        }
        
        public boolean hasMoreElements() {
            
            if (index > items.length)
                index = 0;
            
            Casilla casilla;
            
            for ( ; index < items.length; index++) {
                casilla = items[index];
                if (casilla.state == STATE_OCUPADO)
                {
                    return true;
                }
            }
            //index = 0;
            return false;
        }

        public T nextElement() {
            
            Casilla<K, V> item = items[index];
            
            index++;
            
            return (type == KEYS) ? (T) item.getKey(): 
                    ((type == VALUES) ? (T) item.getValue() : (T) item);
        }
    }
    
    private class ValueCollection extends AbstractCollection<V>
    {

        @Override
        public Iterator<V> iterator() {
            throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
        }

        @Override
        public int size() {
            throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
        }
        
    }
}
