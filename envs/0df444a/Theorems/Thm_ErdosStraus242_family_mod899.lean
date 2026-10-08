-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod899
-- name    : ErdosStraus242.family_mod899
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T17:52:01.093242+00:00
-- url     : https://prove2.me/theorems/9b0081ba-4914-4eb9-b046-ac0109c68571
-- title:
--   Eight Erdős–Straus congruence families modulo 899
-- statement:
--   For every integer $n>2$ with $n\bmod 899\in\{895, 887, 879, 863, 839, 799, 719, 599\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 8 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=899$, where $\alpha=225$ and $g$ runs over the divisors $\{1, 3, 5, 9, 15, 25, 45, 75\}$ of $225$; a class is $n\equiv -4g\pmod{899}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $899=4\cdot225-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid225$, $g<225$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod899 (n : ℕ) (hn : 2 < n)
    (hmod : n % 899 ∈ ({895, 887, 879, 863, 839, 799, 719, 599} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
