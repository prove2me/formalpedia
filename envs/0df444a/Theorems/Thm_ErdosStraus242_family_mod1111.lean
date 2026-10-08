-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod1111
-- name    : ErdosStraus242.family_mod1111
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T23:42:00.049371+00:00
-- url     : https://prove2.me/theorems/66411214-faec-4a3b-b0df-c493c5c72252
-- title:
--   Three Erdős–Straus congruence families modulo 1111
-- statement:
--   For every integer $n>2$ with $n\bmod 1111\in\{1107, 1103, 555\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 3 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=1111$, where $\alpha=278$ and $g$ runs over the divisors $\{1, 2, 139\}$ of $278$; a class is $n\equiv -4g\pmod{1111}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $1111=4\cdot278-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid278$, $g<278$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod1111 (n : ℕ) (hn : 2 < n)
    (hmod : n % 1111 ∈ ({1107, 1103, 555} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
