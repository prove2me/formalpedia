-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod971
-- name    : ErdosStraus242.family_mod971
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T17:52:18.292349+00:00
-- url     : https://prove2.me/theorems/296bf4fa-38cf-4e7a-b1a1-9723ef9aa668
-- title:
--   Five Erdős–Straus congruence families modulo 971
-- statement:
--   For every integer $n>2$ with $n\bmod 971\in\{967, 959, 935, 863, 647\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 5 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=971$, where $\alpha=243$ and $g$ runs over the divisors $\{1, 3, 9, 27, 81\}$ of $243$; a class is $n\equiv -4g\pmod{971}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $971=4\cdot243-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid243$, $g<243$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod971 (n : ℕ) (hn : 2 < n)
    (hmod : n % 971 ∈ ({967, 959, 935, 863, 647} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
