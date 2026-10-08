-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod1091
-- name    : ErdosStraus242.family_mod1091
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T23:41:58.244904+00:00
-- url     : https://prove2.me/theorems/6cc1b804-6bbd-42d0-85e1-0ac75d77b70c
-- title:
--   Seven Erdős–Straus congruence families modulo 1091
-- statement:
--   For every integer $n>2$ with $n\bmod 1091\in\{1087, 1079, 1063, 1039, 1007, 935, 727\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 7 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=1091$, where $\alpha=273$ and $g$ runs over the divisors $\{1, 3, 7, 13, 21, 39, 91\}$ of $273$; a class is $n\equiv -4g\pmod{1091}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $1091=4\cdot273-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid273$, $g<273$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod1091 (n : ℕ) (hn : 2 < n)
    (hmod : n % 1091 ∈ ({1087, 1079, 1063, 1039, 1007, 935, 727} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
