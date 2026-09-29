-- Prove2me | Theorems.Thm_Erdos142_r_three_eq_rothNumberNat
-- name    : Erdos142.r_three_eq_rothNumberNat
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:34:27.288115+00:00
-- url     : https://prove2.me/theorems/1388e7f2-f7a4-4dd5-999d-d87cf330ed9d
-- title:
--   $r_3(N)$ is Mathlib's Roth number
-- statement:
--   For every $N$,
--
--   $$r_3(N) \;=\; \operatorname{rothNumberNat}(N).$$
--
--   Here $r_3(N)$ is the largest size of a subset of $\{1,\dots,N\}$ with no non-trivial three-term arithmetic progression, as defined in this mission, and $\operatorname{rothNumberNat}(N)$ is Mathlib's Roth number: the largest size of a subset of $\{0,1,\dots,N-1\}$ satisfying Mathlib's `ThreeAPFree` condition, namely that $a + c = 2b$ with $a,b,c$ in the set forces $a = b$.
--
--   The two definitions differ in two respects — the ground set is shifted by one, and progression-freeness is expressed by a forbidden triple rather than by a forbidden pair $(a,d)$ with $d>0$ — and this identity says that neither difference matters. Its role in the mission is to anchor the definition: it certifies that the mission's `APFree` and `r` agree with an independently written, widely used formalization, so that no mis-quantified or vacuous definition can propagate into the harder milestones. It also makes the whole of Mathlib's three-term theory, including Behrend's construction, directly available to this mission.
-- source:
--   Erdős Problem #142, https://www.erdosproblems.com/142 (cited there as [Er80, p.92], [Er81, p.4], [Er97c], [Va99, 1.27]); Mathlib, Mathlib/Combinatorics/Additive/AP/Three/Defs.lean, definitions `ThreeAPFree` and `rothNumberNat`.

import Mathlib
import Definitions.Def_Erdos142Basic

namespace Erdos142

theorem r_three_eq_rothNumberNat (N : ℕ) : r 3 N = rothNumberNat N := by sorry

end Erdos142
