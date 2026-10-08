-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod851
-- name    : ErdosStraus242.family_mod851
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T17:51:38.36834+00:00
-- url     : https://prove2.me/theorems/b1e7da24-2a78-4f29-a5ee-a2c8f2e819de
-- title:
--   Three Erdős–Straus congruence families modulo 851
-- statement:
--   For every integer $n>2$ with $n\bmod 851\in\{847, 839, 567\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 3 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=851$, where $\alpha=213$ and $g$ runs over the divisors $\{1, 3, 71\}$ of $213$; a class is $n\equiv -4g\pmod{851}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $851=4\cdot213-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid213$, $g<213$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod851 (n : ℕ) (hn : 2 < n)
    (hmod : n % 851 ∈ ({847, 839, 567} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
