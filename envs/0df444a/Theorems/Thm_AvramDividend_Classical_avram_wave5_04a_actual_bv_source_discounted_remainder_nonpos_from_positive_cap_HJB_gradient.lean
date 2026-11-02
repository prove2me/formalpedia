-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_discounted_remainder_nonpos_from_positive_cap_HJB_gradient
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_source_discounted_remainder_nonpos_from_positive_cap_HJB_gradient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:54:51.22618+00:00
-- url     : https://prove2.me/theorems/8f5999b2-9e94-4eb9-bdde-9b59ac11acbf
-- title:
--   Actual BV source remainder has nonpositive exponentially discounted stopped contribution under positive-cap HJB gradient
-- statement:
--   For the actual original spectrally negative Lévy process with bounded variation, under the positive-cap HJB condition w'(y)≥1 in the open interval 0<y<C, almost surely its explicitly defined nondecreasing downward source residual has a nonpositive exponentially discounted derivative-weighted sum on every stopped ordered partition whose sampled controlled reserve lies within that interval. No global monotonicity of w, pure-jump equality or controlled Itô–Meyer identification is assumed. This is the exact source-side sign required for the final positive-cap verification target.
-- source:
--   Chat04-A BV source proposition designed for final target ef7e6c20-a118-46f0-ac94-5b02204bba49, via canonically Proved original-source local-gradient weighted sign b623ab75-62e9-4ee8-862e-c7ede382a174 and the strict positivity of Real.exp.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_remainder_local_gradient_weighted_stopped_nonpos

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The positive-cap HJB gradient condition yields the correct discounted
nonpositive downward original-source BV residual term along interior
stopped reserve partitions, independently of controlled Ito-Meyer. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_source_discounted_remainder_nonpos_from_positive_cap_HJB_gradient
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
        (hinterior : ∀ i : Fin n,
          0 < riskProcess X x D (u i) ω ∧
            ENNReal.ofReal (riskProcess X x D (u i) ω) < C),
        (∑ i : Fin n,
          -(Real.exp (-(q * (u i : ℝ))) *
            deriv w (riskProcess X x D (u i) ω)) *
              (R (u (i + 1)) - R (u i))) ≤ 0 := by sorry
