-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod923
-- name    : ErdosStraus242.family_mod923
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T17:52:09.714837+00:00
-- url     : https://prove2.me/theorems/88d7c3bd-e098-42fb-bca7-2a8e4352e303
-- title:
--   Seven Erdős–Straus congruence families modulo 923
-- statement:
--   For every integer $n>2$ with $n\bmod 923\in\{919, 911, 895, 879, 839, 791, 615\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 7 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=923$, where $\alpha=231$ and $g$ runs over the divisors $\{1, 3, 7, 11, 21, 33, 77\}$ of $231$; a class is $n\equiv -4g\pmod{923}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $923=4\cdot231-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid231$, $g<231$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod923 (n : ℕ) (hn : 2 < n)
    (hmod : n % 923 ∈ ({919, 911, 895, 879, 839, 791, 615} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
