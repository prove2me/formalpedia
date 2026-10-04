-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod127
-- name    : ErdosStraus242.family_mod127
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T06:36:51.662737+00:00
-- url     : https://prove2.me/theorems/575dad36-5651-49fd-b15b-b32a728b875d
-- title:
--   Five Erdős–Straus congruence families modulo 127
-- statement:
--   For every integer $n>2$ with $n\bmod 127\in\{123,119,111,95,63\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The five classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=127$, where $\alpha=32$ and $g\in\{1,2,4,8,16\}$ runs over the divisors of $32$; a class is $n\equiv -4g\pmod{127}$. The modulus 127 is coprime to $840$ and absent from the existing 39-family frontier; each class contains hard-core primes surviving all 39 sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $127=4\cdot 32-1$ from the triples $(a,c,d)=(1,32,1),(1,16,2),(1,8,4),(1,4,8),(1,2,16)$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod127 (n : ℕ) (hn : 2 < n)
    (hmod : n % 127 ∈ ({123, 119, 111, 95, 63} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
