-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod823
-- name    : ErdosStraus242.family_mod823
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T09:32:36.255093+00:00
-- url     : https://prove2.me/theorems/d5f88114-f871-4885-9083-d8c87d5d30c7
-- title:
--   Three Erdős–Straus congruence families modulo 823
-- statement:
--   For every integer $n>2$ with $n\bmod 823\in\{819, 815, 411\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 3 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=823$, where $\alpha=206$ and $g$ runs over the divisors $\{1, 2, 103\}$ of $206$; a class is $n\equiv -4g\pmod{823}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $823=4\cdot206-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid206$, $g<206$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod823 (n : ℕ) (hn : 2 < n)
    (hmod : n % 823 ∈ ({819, 815, 411} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
