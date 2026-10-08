-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod967
-- name    : ErdosStraus242.family_mod967
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T17:52:15.641895+00:00
-- url     : https://prove2.me/theorems/1bfe5abf-bb58-401a-9f24-1411edadd5f0
-- title:
--   Five Erdős–Straus congruence families modulo 967
-- statement:
--   For every integer $n>2$ with $n\bmod 967\in\{963, 959, 923, 879, 483\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 5 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=967$, where $\alpha=242$ and $g$ runs over the divisors $\{1, 2, 11, 22, 121\}$ of $242$; a class is $n\equiv -4g\pmod{967}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $967=4\cdot242-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid242$, $g<242$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod967 (n : ℕ) (hn : 2 < n)
    (hmod : n % 967 ∈ ({963, 959, 923, 879, 483} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
