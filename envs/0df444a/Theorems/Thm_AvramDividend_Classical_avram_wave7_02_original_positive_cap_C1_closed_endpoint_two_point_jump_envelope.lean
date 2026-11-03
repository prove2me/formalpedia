-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
-- name    : AvramDividend.Classical.avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:07:52.456788+00:00
-- url     : https://prove2.me/theorems/aeec073e-64c0-49d6-a86e-3113d03c0485
-- title:
--   Canonical positive-cap C1 two-point dividend envelope remains valid at the closed cap boundary
-- statement:
--   For the original Avram C1 candidate with unit lower derivative on the strict positive-cap interior, continuity on nonnegative reserves extends the two-point dividend-value inequality to compact intervals Icc 0 b with ENNReal.ofReal b≤C, including b exactly at the cap. For 0≤y≤z≤b, z-y≤w(z)-w(y). This removes the strict-cap limitation from the right-dividend jump inequality and is directly relevant to the canonical original barrier and time-zero reserve at cap equality.
-- source:
--   Pinned Mathlib derivative monotonicity on Icc 0 b and strictly monotone ENNReal.ofReal on nonnegative arguments. The actual generator smoothness is only required on the open interior (0,b); the endpoint uses continuousOn. No surrogate process.

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
open Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (b : ℝ) (hb : 0 ≤ b) (hbC : ENNReal.ofReal b ≤ C) :
    ∀ y ∈ Icc (0 : ℝ) b, ∀ z ∈ Icc (0 : ℝ) b,
      y ≤ z → z - y ≤ w z - w y := by sorry
