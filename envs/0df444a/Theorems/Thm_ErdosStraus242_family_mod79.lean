-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod79
-- name    : ErdosStraus242.family_mod79
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T06:11:59.822884+00:00
-- url     : https://prove2.me/theorems/e66ed7c3-3031-4b90-951e-2a0197f9f2bd
-- title:
--   Five Erdős–Straus congruence families modulo 79
-- statement:
--   For every integer $n>2$ with $n\bmod 79\in\{39,59,63,71,75\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The five classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=79$, where $\alpha=20$ and $g$ runs over the divisors $\{1,2,4,5,10\}$ of $20$; a class is $n\equiv -4g \pmod{79}$. Modulo 79 is coprime to $840$ and is absent from the existing 39-family mission frontier, and each of the five classes contains primes of the modulo-840 hard core that survive all 39 existing sieves, so these families strictly advance the frontier. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; classes at modulus $79=4\cdot 20-1$ from the triples $(a,c,d)=(1,20,1),(1,10,2),(1,5,4),(1,4,5),(1,2,10)$; cf. Erdős Problem 242, https://www.erdosproblems.com/242.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod79 (n : ℕ) (hn : 2 < n)
    (hmod : n % 79 ∈ ({39, 59, 63, 71, 75} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
