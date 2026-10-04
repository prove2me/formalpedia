-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod703
-- name    : ErdosStraus242.family_mod703
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T09:32:19.379975+00:00
-- url     : https://prove2.me/theorems/9bd6a745-e759-4d85-9588-79cdea0be404
-- title:
--   Nine Erdős–Straus congruence families modulo 703
-- statement:
--   For every integer $n>2$ with $n\bmod 703\in\{699, 695, 687, 671, 659, 639, 615, 527, 351\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 9 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=703$, where $\alpha=176$ and $g$ runs over the divisors $\{1, 2, 4, 8, 11, 16, 22, 44, 88\}$ of $176$; a class is $n\equiv -4g\pmod{703}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $703=4\cdot176-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid176$, $g<176$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod703 (n : ℕ) (hn : 2 < n)
    (hmod : n % 703 ∈ ({699, 695, 687, 671, 659, 639, 615, 527, 351} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
