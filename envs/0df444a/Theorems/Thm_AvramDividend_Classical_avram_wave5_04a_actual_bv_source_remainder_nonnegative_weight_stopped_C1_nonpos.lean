-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_remainder_nonnegative_weight_stopped_C1_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_source_remainder_nonnegative_weight_stopped_C1_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:45:25.4252+00:00
-- url     : https://prove2.me/theorems/e8f3ede9-fa96-49a0-a52d-d30279929abe
-- title:
--   Stopped increasing-C1 contribution of the actual original BV source remainder is nonpositive for arbitrary nonnegative weights
-- statement:
--   For the actual bounded-variation spectrally negative Levy source, almost surely the unique residual obtained by subtracting the full intrinsic negative source left-jump series from drift minus source position is nondecreasing. For every admissible dividend strategy and increasing C1 test function w, every samplewise stopped ordered partition, and any nonnegative weights (including exponential discount factors), the derivative-weighted residual variation sum is nonpositive. No Itô–Meyer integration or pure-jump identity is assumed.
-- source:
--   Chat04-A original-process helper, constructed directly from canonical Proved original source monotone residual 019edf01-4961-4bf1-805e-b935366106bb and Lean finite sum inequalities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_canonical_remainder_monotone

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- For the actual bounded-variation source, any nonnegative time weights
preserve the downward sign of the stopped C1 source-residual variation.
The weights may specialise to discount factors; this is not Ito-Meyer. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_source_remainder_nonnegative_weight_stopped_C1_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw : Monotone w) :
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
        (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i),
        (∑ i : Fin n,
          -(a i * deriv w (riskProcess X x D (u i) ω)) *
            (R (u (i + 1)) - R (u i))) ≤ 0 := by sorry
