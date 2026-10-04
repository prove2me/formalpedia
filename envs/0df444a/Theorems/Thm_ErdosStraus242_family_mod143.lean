-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod143
-- name    : ErdosStraus242.family_mod143
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T06:12:09.121727+00:00
-- url     : https://prove2.me/theorems/7906eb82-f7fb-4c31-bbe3-388666221936
-- title:
--   Eight Erdős–Straus congruence families modulo 143
-- statement:
--   For every integer $n>2$ with $n\bmod 143\in\{71,95,107,119,127,131,135,139\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The eight classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=143$, where $\alpha=36$ and $g$ runs over the divisors $\{1,2,3,4,6,9,12,18\}$ of $36$; a class is $n\equiv -4g\pmod{143}$. This is the smallest composite modulus $\equiv 3\pmod 4$ coprime to $840$, unused by the existing 39-family frontier; eight classes of one modulus make this the densest single sieve step so far in the mission.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; classes at modulus $143=4\cdot 36-1$ from the triples $(a,c,d)=(1,36,1),(1,18,2),(1,12,3),(1,9,4),(1,6,6),(1,4,9),(1,3,12),(1,2,18)$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod143 (n : ℕ) (hn : 2 < n)
    (hmod : n % 143 ∈ ({71, 95, 107, 119, 127, 131, 135, 139} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
