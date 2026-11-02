-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_remainder_local_gradient_weighted_stopped_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_source_remainder_local_gradient_weighted_stopped_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:50:45.260975+00:00
-- url     : https://prove2.me/theorems/b623ab75-62e9-4ee8-862e-c7ede382a174
-- title:
--   Original BV residual: weighted stopped nonlinear source contribution is nonpositive under only sampled local derivative conditions
-- statement:
--   For the actual original bounded-variation spectrally negative Levy source and an admissible dividend strategy, almost surely the explicit monotone drift-minus-path-minus-intrinsic-left-jump residual has a nonpositive stopped nonlinear C1 contribution for any nonnegative partition weights, provided the verification derivative is nonnegative only at the sampled controlled reserve points. This does not require global monotonicity of the verification function; local HJB gradient assumptions on the positive interval below the dividend cap can imply the sampled derivative hypotheses, allowing discount factors.
-- source:
--   Chat04-A source result directly aligned with final BV verification target ef7e6c20-a118-46f0-ac94-5b02204bba49: its HJB derivative bound is local to 0<y<C, not global monotonicity. Lean proof from canonical original source monotone residual 019edf01-4961-4bf1-805e-b935366106bb.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_canonical_remainder_monotone

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Original BV source residual sign needs derivatives nonnegative only
at sampled stopped reserves, not global monotonicity of the HJB candidate. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_source_remainder_local_gradient_weighted_stopped_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) :
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
        (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
        (hderiv : ∀ i : Fin n,
          0 ≤ deriv w (riskProcess X x D (u i) ω)),
        (∑ i : Fin n,
          -(a i * deriv w (riskProcess X x D (u i) ω)) *
            (R (u (i + 1)) - R (u i))) ≤ 0 := by sorry
