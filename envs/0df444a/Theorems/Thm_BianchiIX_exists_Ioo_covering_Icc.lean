-- Prove2me | Theorems.Thm_BianchiIX_exists_Ioo_covering_Icc
-- name    : BianchiIX.exists_Ioo_covering_Icc
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T00:33:38.411284+00:00
-- url     : https://prove2.me/theorems/1f37c13e-fc27-45d3-a7e4-082408d1567c
-- title:
--   An open interval neighborhood of a closed interval in an open set
-- statement:
--   If $s\leq t$, $U\subset\mathbb R$ is open, and
--   $[s,t]\subset U$, then there are $l<s$ and $r>t$ such that $(l,r)\subset U$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/IntervalNeighborhood.lean#L11-L25

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

theorem BianchiIX.exists_Ioo_covering_Icc {s t : ℝ} {U : Set ℝ} (hst : s ≤ t)
    (hU : IsOpen U) (hsub : Icc s t ⊆ U) :
    ∃ l r : ℝ, l < s ∧ t < r ∧ Ioo l r ⊆ U := by sorry
