-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod611
-- name    : ErdosStraus242.family_mod611
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T09:31:53.467862+00:00
-- url     : https://prove2.me/theorems/172fcc59-1b1f-48b1-b9a9-d80be4d2ae39
-- title:
--   Five Erdős–Straus congruence families modulo 611
-- statement:
--   For every integer $n>2$ with $n\bmod 611\in\{607, 599, 575, 543, 407\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 5 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=611$, where $\alpha=153$ and $g$ runs over the divisors $\{1, 3, 9, 17, 51\}$ of $153$; a class is $n\equiv -4g\pmod{611}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $611=4\cdot153-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid153$, $g<153$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod611 (n : ℕ) (hn : 2 < n)
    (hmod : n % 611 ∈ ({607, 599, 575, 543, 407} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
