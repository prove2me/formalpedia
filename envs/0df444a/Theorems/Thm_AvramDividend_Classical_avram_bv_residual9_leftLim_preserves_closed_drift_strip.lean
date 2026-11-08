-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_leftLim_preserves_closed_drift_strip
-- name    : AvramDividend.Classical.avram_bv_residual9_leftLim_preserves_closed_drift_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:23:31.064246+00:00
-- url     : https://prove2.me/theorems/4bed68fe-299b-427e-a510-efc81372fe1a
-- title:
--   Left limits preserve a deterministic closed pre-ruin reserve strip
-- statement:
--   For an original process whose reserve stays in a fixed closed real interval at all times at or before a grid point, the literal Function.leftLim at that point stays in the same interval. Uses the pinned Mathlib closed-set cluster-point theorem, with no artificial continuity or integrability hypothesis.
-- source:
--   AVRAM BV-RESIDUAL9 round-five source-exact left-limit envelope

import Mathlib
open Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_leftLim_preserves_closed_drift_strip
    (f : ℝ≥0 → ℝ) (a : ℝ≥0) (L U : ℝ)
    (hf : ∀ t : ℝ≥0, t ≤ a → L ≤ f t ∧ f t ≤ U) :
    L ≤ Function.leftLim f a ∧ Function.leftLim f a ≤ U := by sorry
