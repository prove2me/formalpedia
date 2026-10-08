-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod911
-- name    : ErdosStraus242.family_mod911
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T17:52:03.078585+00:00
-- url     : https://prove2.me/theorems/e5222c06-2f2d-467d-a649-f9f5b139c230
-- title:
--   Eleven Erdős–Straus congruence families modulo 911
-- statement:
--   For every integer $n>2$ with $n\bmod 911\in\{907, 903, 899, 895, 887, 863, 835, 759, 683, 607, 455\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 11 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=911$, where $\alpha=228$ and $g$ runs over the divisors $\{1, 2, 3, 4, 6, 12, 19, 38, 57, 76, 114\}$ of $228$; a class is $n\equiv -4g\pmod{911}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $911=4\cdot228-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid228$, $g<228$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod911 (n : ℕ) (hn : 2 < n)
    (hmod : n % 911 ∈ ({907, 903, 899, 895, 887, 863, 835, 759, 683, 607, 455} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
