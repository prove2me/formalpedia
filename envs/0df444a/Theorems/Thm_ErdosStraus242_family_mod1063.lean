-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod1063
-- name    : ErdosStraus242.family_mod1063
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T23:41:50.039358+00:00
-- url     : https://prove2.me/theorems/db1131f7-f1d5-479e-acc8-e9b4cc84589a
-- title:
--   Seven Erdős–Straus congruence families modulo 1063
-- statement:
--   For every integer $n>2$ with $n\bmod 1063\in\{1059, 1055, 1035, 1007, 987, 911, 531\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 7 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=1063$, where $\alpha=266$ and $g$ runs over the divisors $\{1, 2, 7, 14, 19, 38, 133\}$ of $266$; a class is $n\equiv -4g\pmod{1063}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $1063=4\cdot266-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid266$, $g<266$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod1063 (n : ℕ) (hn : 2 < n)
    (hmod : n % 1063 ∈ ({1059, 1055, 1035, 1007, 987, 911, 531} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
