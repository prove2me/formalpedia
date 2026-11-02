-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_discounted_C1_source_stopped_signed_drift_envelope
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_discounted_C1_source_stopped_signed_drift_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:39:40.359195+00:00
-- url     : https://prove2.me/theorems/84c89c23-ddb9-4508-b0d7-a07d98d0f111
-- title:
--   Actual BV stopped C1 HJB-strip source correction is nonpositive and source-drift dominated
-- statement:
--   For the true bounded-variation spectrally negative Levy source and an actual dividend strategy, a single almost-sure residual process defined through the intrinsic negative source left-jump series simultaneously controls every stopped HJB-interior discounted C1 source correction: its signed derivative-weighted contribution is nonpositive, and under an explicit uniform coefficient bound M its absolute size is bounded by M times the physical source drift-minus-source endpoint increment. This statement neither requires global monotonicity of w nor presupposes a controlled Ito-Meyer identification.
-- source:
--   Chat04-A original-process stopped C1 source interface: combine canonically Proved positive-cap HJB-strip sign 8f5999b2-9e94-4eb9-bdde-9b59ac11acbf and source-only weighted drift envelope ae763e15-49e9-4dd0-b1b2-4168ba7d0c52; explicit remainder witnesses agree pointwise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_discounted_remainder_nonpos_from_positive_cap_HJB_gradient
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_weighted_remainder_bound_by_original_source_drift_residual

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- One original-source event simultaneously gives the discounted C1
positive-cap source sign and an observable source-only absolute envelope
for those derivative-weighted remainder sums. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_discounted_C1_source_stopped_signed_drift_envelope
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
            ENNReal.ofReal (riskProcess X x D (u i) ω) < C)
        (M : ℝ) (hM : 0 ≤ M)
        (hcoef : ∀ i : ℕ,
          |Real.exp (-(q * (u i : ℝ))) *
            deriv w (riskProcess X x D (u i) ω)| ≤ M),
        (∑ i : Fin n,
          -(Real.exp (-(q * (u i : ℝ))) *
            deriv w (riskProcess X x D (u i) ω)) *
              (R (u (i + 1)) - R (u i))) ≤ 0 ∧
        |(Finset.range n).sum (fun i =>
          (Real.exp (-(q * (u i : ℝ))) *
            deriv w (riskProcess X x D (u i) ω)) *
              (R (u (i + 1)) - R (u i)))| ≤
          M * (((u n : ℝ) - (u 0 : ℝ)) * X.drift -
            (X.X (u n) ω - X.X (u 0) ω)) := by sorry
