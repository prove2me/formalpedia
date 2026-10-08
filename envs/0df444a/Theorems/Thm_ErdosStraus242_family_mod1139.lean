-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod1139
-- name    : ErdosStraus242.family_mod1139
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T23:42:05.949532+00:00
-- url     : https://prove2.me/theorems/725c6331-2926-4a56-b92e-917f4ee44dae
-- title:
--   Seven Erdős–Straus congruence families modulo 1139
-- statement:
--   For every integer $n>2$ with $n\bmod 1139\in\{1135, 1127, 1119, 1079, 1063, 911, 759\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 7 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=1139$, where $\alpha=285$ and $g$ runs over the divisors $\{1, 3, 5, 15, 19, 57, 95\}$ of $285$; a class is $n\equiv -4g\pmod{1139}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $1139=4\cdot285-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid285$, $g<285$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod1139 (n : ℕ) (hn : 2 < n)
    (hmod : n % 1139 ∈ ({1135, 1127, 1119, 1079, 1063, 911, 759} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
