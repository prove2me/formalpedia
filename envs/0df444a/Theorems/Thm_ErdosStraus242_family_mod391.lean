-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod391
-- name    : ErdosStraus242.family_mod391
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T08:56:06.379094+00:00
-- url     : https://prove2.me/theorems/e3093afe-18d7-47c6-8268-c35afa33e4fc
-- title:
--   Five Erdős–Straus congruence families modulo 391
-- statement:
--   For every integer $n>2$ with $n\bmod 391\in\{387, 383, 363, 335, 195\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 5 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=391$, where $\alpha=98$ and $g$ runs over the divisors $\{1, 2, 7, 14, 49\}$ of $98$; a class is $n\equiv -4g\pmod{391}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $391=4\cdot98-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid98$, $g<98$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod391 (n : ℕ) (hn : 2 < n)
    (hmod : n % 391 ∈ ({387, 383, 363, 335, 195} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
