-- Prove2me | Theorems.Thm_AKSZigZag_section3_bounded_depth_halvers
-- name    : AKSZigZag.section3_bounded_depth_halvers
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:19:38.469302+00:00
-- url     : https://prove2.me/theorems/ca5014c4-7975-44d4-99a7-0d5160686d07
-- title:
--   §3, p.4 — bounded-depth $\varepsilon$-halvers exist
-- statement:
--   For every $\varepsilon>0$ there is a number $d$ such that for every $m$ some standard comparator network on $m$ registers has depth at most $d$ and is an $\varepsilon$-halver.
--
--   This is the output of §3: the depth bound $d$ depends on $\varepsilon$ only. It feeds the nearsort construction of §4 and through it the whole sorting network.
--
--   Differences from the source:
--   - encoding: a bounded depth ε-halver network → ∃ d, ∀ m, a standard ε-halver on m registers of depth ≤ d; reason: bounded means bounded independently of m
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, §3, p.4 ("We construct now a bounded depth ε-halver network.")

import Mathlib
import Definitions.Def_AKSSorting_Core_ComparatorNetwork
import Definitions.Def_AKSZigZag_IsStandard
import Definitions.Def_AKSZigZag_IsHalver

namespace AKSZigZag

open AKSSorting.Core

/-- **Bounded-depth ε-halvers exist** (AKS, STOC 1983, doi:10.1145/800061.808726, §3, p.4): "We
construct now a bounded depth ε-halver network." For every `ε > 0` there is a depth `d` such that
for every `m` some standard comparator network on `m` registers of depth at most `d` is an
ε-halver. -/
theorem section3_bounded_depth_halvers (ε : ℝ) (hε : 0 < ε) :
    ∃ d : ℕ, ∀ m : ℕ, ∃ N : ComparatorNetwork m,
      IsStandard N ∧ N.depth ≤ d ∧ IsHalver ε N := by sorry

end AKSZigZag
