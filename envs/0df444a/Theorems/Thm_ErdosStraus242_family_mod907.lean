-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod907
-- name    : ErdosStraus242.family_mod907
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T17:52:02.463603+00:00
-- url     : https://prove2.me/theorems/d245878d-0722-44b1-93ca-f6440b78a8c2
-- title:
--   One Erdős–Straus congruence families modulo 907
-- statement:
--   For every integer $n>2$ with $n\bmod 907\in\{903\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 1 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=907$, where $\alpha=227$ and $g$ runs over the divisors $\{1\}$ of $227$; a class is $n\equiv -4g\pmod{907}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $907=4\cdot227-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid227$, $g<227$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod907 (n : ℕ) (hn : 2 < n)
    (hmod : n % 907 ∈ ({903} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
