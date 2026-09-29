-- Prove2me | Theorems.Thm_ErdosStraus242_hard_core_840_after_mod11_mod19_mod23
-- name    : ErdosStraus242.hard_core_840_after_mod11_mod19_mod23
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-11T20:47:45.083993+00:00
-- url     : https://prove2.me/theorems/f9748a25-ef53-43a6-945b-a5eb519613a9
-- title:
--   Remaining modulo-840 prime cases after the modulo 11, 19 and 23 sieves
-- statement:
--   Let $p>2$ be prime. Assume $p \bmod 840 \in \{1,121,169,289,361,529\}$, $p\bmod 11\notin\{7,8,10\}$, $p\bmod 19\notin\{14,15,18\}$ and $p\bmod 23\notin\{7,10,11,15,17,19,20,21,22\}$. The assertion is that there are natural numbers $1\le x<y<z$ with
--   $$\frac4p=\frac1x+\frac1y+\frac1z .$$
--
--   This is the residual part of Erdős Problem 242 that remains after removing from the frontier `ErdosStraus242.hard_core_840_after_mod11` the classes settled by `ErdosStraus242.family_mod19` and `ErdosStraus242.family_mod23`, the two further specializations of the Bloom–Elsholtz parametrization at $4acd-1=19$ and $4acd-1=23$. Together with those two families it recovers that frontier, so nothing is lost by the restriction.
--
--   The excluded classes are not empty of the six residues modulo $840$: among the $511$ primes below $2\cdot10^5$ in the six classes, $150$ survive the three sieves, the smallest being $1201$. No claim of a proof is made here; this node names what is left open after the sieve, and keeps the mission's strict denominator convention.
-- source:
--   Erdős Problem 242, https://www.erdosproblems.com/242, restricted from the mission frontier ErdosStraus242.hard_core_840_after_mod11. The additional exclusions are the classes covered by the Bloom–Elsholtz parametrization at 4acd-1 = 19 and 23, p. 239, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf. This residual formulation is a decomposition made here, not a quoted result.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem hard_core_840_after_mod11_mod19_mod23 (p : ℕ) (hp : Nat.Prime p) (hp2 : 2 < p)
    (hres : p % 840 ∈ ({1, 121, 169, 289, 361, 529} : Finset ℕ))
    (h11 : p % 11 ∉ ({7, 8, 10} : Finset ℕ))
    (h19 : p % 19 ∉ ({14, 15, 18} : Finset ℕ))
    (h23 : p % 23 ∉ ({7, 10, 11, 15, 17, 19, 20, 21, 22} : Finset ℕ)) :
    IsErdosStraus p := by sorry
end ErdosStraus242
