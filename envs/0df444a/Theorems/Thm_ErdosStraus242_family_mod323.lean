-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod323
-- name    : ErdosStraus242.family_mod323
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T07:38:10.136863+00:00
-- url     : https://prove2.me/theorems/23889edf-ce11-4631-ade1-0dc1a017d94f
-- title:
--   Four Erdős–Straus congruence families modulo 323
-- statement:
--   For every integer $n>2$ with $n\bmod 323\in\{319, 311, 287, 215\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The four classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=323$, where $\alpha=81$ and $g$ runs over the divisors \{1,3,9,27\} of $81$; a class is $n\equiv -4g\pmod{323}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $323=4\cdot81-1$ from the triples $(a,c,d)=(1,81,1),(1,27,3),(1,9,9),(1,3,27)$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod323 (n : ℕ) (hn : 2 < n)
    (hmod : n % 323 ∈ ({319, 311, 287, 215} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
