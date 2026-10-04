-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod299
-- name    : ErdosStraus242.family_mod299
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T07:38:02.040698+00:00
-- url     : https://prove2.me/theorems/f9c973ef-a6df-4b9e-8f02-9a866260ad1c
-- title:
--   Five Erdős–Straus congruence families modulo 299
-- statement:
--   For every integer $n>2$ with $n\bmod 299\in\{295, 287, 279, 239, 199\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The five classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=299$, where $\alpha=75$ and $g$ runs over the divisors \{1,3,5,15,25\} of $75$; a class is $n\equiv -4g\pmod{299}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $299=4\cdot75-1$ from the triples $(a,c,d)=(1,75,1),(1,25,3),(1,15,5),(1,5,15),(1,3,25)$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod299 (n : ℕ) (hn : 2 < n)
    (hmod : n % 299 ∈ ({295, 287, 279, 239, 199} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
