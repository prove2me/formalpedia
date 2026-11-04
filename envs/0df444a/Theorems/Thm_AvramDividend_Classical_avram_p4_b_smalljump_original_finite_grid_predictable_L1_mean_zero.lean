-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_grid_predictable_L1_mean_zero
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_finite_grid_predictable_L1_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:57:31.74745+00:00
-- url     : https://prove2.me/theorems/d706f34d-96b4-4c3e-aa23-577e546e706b
-- title:
--   Original Levy finite-grid bounded predictable compensated count has zero physical mean
-- statement:
--   A finite sum of genuinely original intrinsic finite-band compensated Levy marked jump counts with random bounded original-right-continuous-past measurable predictable coefficients has zero physical expectation, conditional on each original source count finite first moment and conditional mean-zero P2 interface.
-- source:
--   Actual source SpectrallyNegativeLevy and two previously Proved P4-B conditional centring and zero-mean helpers; P2 rate remains an explicit hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_bounded_predictable_weight_count_condExp_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_weight_condExp_zero_implies_mean_zero

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_finite_grid_predictable_L1_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ≥0) (B : ι → Set ℝ)
    (J : ι → Ω → ℝ≥0∞)
    (hJsource : ∀ i ω, J i ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc (s i) (t i) ×ˢ B i))
    (rate : ι → ℝ≥0∞)
    (hYint : ∀ i ∈ S,
      Integrable (fun ω => (J i ω).toReal - (rate i).toReal) P)
    (hYcenter : ∀ i ∈ S,
      P[(fun ω => (J i ω).toReal - (rate i).toReal) |
        𝓕.rightCont (s i)] =ᵐ[P] 0)
    (H : ι → Ω → ℝ) (C : ι → ℝ)
    (hH : ∀ i ∈ S,
      StronglyMeasurable[𝓕.rightCont (s i)] (H i))
    (hBound : ∀ i ∈ S, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ C i) :
    (∫ ω, ∑ i ∈ S,
      H i ω * ((J i ω).toReal - (rate i).toReal) ∂P) = 0 := by sorry
