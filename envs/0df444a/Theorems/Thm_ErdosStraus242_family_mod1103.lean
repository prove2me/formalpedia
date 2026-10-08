-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod1103
-- name    : ErdosStraus242.family_mod1103
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T23:41:59.687347+00:00
-- url     : https://prove2.me/theorems/08fa3f64-0aa4-418e-bcd0-9769d119fc97
-- title:
--   Eleven Erdős–Straus congruence families modulo 1103
-- statement:
--   For every integer $n>2$ with $n\bmod 1103\in\{1099, 1095, 1091, 1087, 1079, 1055, 1011, 919, 827, 735, 551\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 11 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=1103$, where $\alpha=276$ and $g$ runs over the divisors $\{1, 2, 3, 4, 6, 12, 23, 46, 69, 92, 138\}$ of $276$; a class is $n\equiv -4g\pmod{1103}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $1103=4\cdot276-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid276$, $g<276$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod1103 (n : ℕ) (hn : 2 < n)
    (hmod : n % 1103 ∈ ({1099, 1095, 1091, 1087, 1079, 1055, 1011, 919, 827, 735, 551} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
