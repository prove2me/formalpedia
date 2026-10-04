-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod839
-- name    : ErdosStraus242.family_mod839
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T09:32:38.730403+00:00
-- url     : https://prove2.me/theorems/97c20031-9cca-419b-886a-2d23f203f120
-- title:
--   Fifteen Erdős–Straus congruence families modulo 839
-- statement:
--   For every integer $n>2$ with $n\bmod 839\in\{835, 831, 827, 819, 815, 811, 799, 783, 779, 755, 719, 699, 671, 559, 419\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 15 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=839$, where $\alpha=210$ and $g$ runs over the divisors $\{1, 2, 3, 5, 6, 7, 10, 14, 15, 21, 30, 35, 42, 70, 105\}$ of $210$; a class is $n\equiv -4g\pmod{839}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $839=4\cdot210-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid210$, $g<210$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod839 (n : ℕ) (hn : 2 < n)
    (hmod : n % 839 ∈ ({835, 831, 827, 819, 815, 811, 799, 783, 779, 755, 719, 699, 671, 559, 419} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
