-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod1151
-- name    : ErdosStraus242.family_mod1151
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T23:42:08.463601+00:00
-- url     : https://prove2.me/theorems/1094f9bf-cfbe-4b2f-9d1e-f685f918aa2e
-- title:
--   Seventeen Erdős–Straus congruence families modulo 1151
-- statement:
--   For every integer $n>2$ with $n\bmod 1151\in\{1147, 1143, 1139, 1135, 1127, 1119, 1115, 1103, 1087, 1079, 1055, 1023, 1007, 959, 863, 767, 575\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 17 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=1151$, where $\alpha=288$ and $g$ runs over the divisors $\{1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 32, 36, 48, 72, 96, 144\}$ of $288$; a class is $n\equiv -4g\pmod{1151}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $1151=4\cdot288-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid288$, $g<288$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod1151 (n : ℕ) (hn : 2 < n)
    (hmod : n % 1151 ∈ ({1147, 1143, 1139, 1135, 1127, 1119, 1115, 1103, 1087, 1079, 1055, 1023, 1007, 959, 863, 767, 575} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
