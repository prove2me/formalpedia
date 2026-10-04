-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod103
-- name    : ErdosStraus242.family_mod103
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T06:36:48.300597+00:00
-- url     : https://prove2.me/theorems/53d4fb50-4e9e-49f0-abae-b04b9ac5a090
-- title:
--   Three Erdős–Straus congruence families modulo 103
-- statement:
--   For every integer $n>2$ with $n\bmod 103\in\{99,95,51\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The three classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=103$, where $\alpha=26$ and $g\in\{1,2,13\}$ runs over the divisors of $26$; a class is $n\equiv -4g\pmod{103}$. The modulus 103 is coprime to $840$ and absent from the existing 39-family frontier; each class contains hard-core primes surviving all 39 sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $103=4\cdot 26-1$ from the triples $(a,c,d)=(1,26,1),(1,13,2),(1,2,13)$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod103 (n : ℕ) (hn : 2 < n)
    (hmod : n % 103 ∈ ({99, 95, 51} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
