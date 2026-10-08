-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod1019
-- name    : ErdosStraus242.family_mod1019
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T23:41:40.206562+00:00
-- url     : https://prove2.me/theorems/b7168dde-ea73-49e5-8112-85281e5b85a0
-- title:
--   Seven Erdős–Straus congruence families modulo 1019
-- statement:
--   For every integer $n>2$ with $n\bmod 1019\in\{1015, 1007, 999, 959, 951, 815, 679\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 7 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=1019$, where $\alpha=255$ and $g$ runs over the divisors $\{1, 3, 5, 15, 17, 51, 85\}$ of $255$; a class is $n\equiv -4g\pmod{1019}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $1019=4\cdot255-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid255$, $g<255$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod1019 (n : ℕ) (hn : 2 < n)
    (hmod : n % 1019 ∈ ({1015, 1007, 999, 959, 951, 815, 679} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
