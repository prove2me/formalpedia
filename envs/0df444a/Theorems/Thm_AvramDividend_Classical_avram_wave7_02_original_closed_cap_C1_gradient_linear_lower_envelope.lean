-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
-- name    : AvramDividend.Classical.avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:06:33.516199+00:00
-- url     : https://prove2.me/theorems/fc03f3ac-1178-466d-bb09-d9cae7a15d5e
-- title:
--   Original BV verification candidate has the gradient lower envelope through the closed cap boundary
-- statement:
--   For the original Avram HJB candidate on any positive extended-real reserve cap C, if the function is continuous on nonnegative reserves, C1 on the strict positive interior and has derivative at least one there, then for every closed-cap reserve b with ENNReal.ofReal b ≤ C, the lower envelope w(y)≥w(0)+y holds for all y in [0,b], including y=b even when b is exactly the finite cap. No derivative at the cap is assumed. The theorem follows by monotonicity of w(y)-y on the closed interval using only interior derivatives, and directly supports W8-04 terminal reserve at an admissible cap boundary.
-- source:
--   Strengthens previously Proved f138f64f-f82c-4fdc-943c-d77f480ba88f, which assumed ENNReal.ofReal b<C. The strict interior subset still follows from hz<b and ENNReal.ofReal b≤C. A closed-interval derivative monotonicity theorem then includes the cap endpoint. No stochastic model alteration or noncanonical hypothesis.

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
open Set
open scoped NNReal ENNReal
noncomputable section

/-- The closed cap boundary needs no derivative at the cap: only the
strictly interior C¹ derivative bound and continuity at the endpoint. -/

theorem AvramDividend.Classical.avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (b : ℝ) (hb : 0 ≤ b) (hbC : ENNReal.ofReal b ≤ C) :
    ∀ y ∈ Icc (0 : ℝ) b, w 0 + y ≤ w y := by sorry
