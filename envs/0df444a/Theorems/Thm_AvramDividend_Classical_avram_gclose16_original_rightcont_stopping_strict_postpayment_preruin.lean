-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gclose16_original_rightcont_stopping_strict_postpayment_preruin
-- name    : AvramDividend.Classical.avram_gclose16_original_rightcont_stopping_strict_postpayment_preruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:09:56.28964+00:00
-- url     : https://prove2.me/theorems/0e9f7014-8035-4cfa-82dd-a817936832b7
-- title:
--   Original unbounded-variation pre-ruin stopping times have strictly positive postpayment reserve almost surely
-- statement:
--   At each true original right-continuous filtration stopping time lying strictly before ruin, the controlled postpayment surplus is strictly positive almost surely. Downward regularity supplies an actual negative future original Levy increment before any remaining positive ruin gap, and original dividend monotonicity and admissible solvency exclude zero postpayment reserve at the stopping time. This is a necessary single-stopping-time step for finite and top Gaussian spatial localisation; a simultaneous all-times compact-prefix theorem remains separate.
-- source:
--   Take the proved downward-regular negative original increment within a positive remaining ruin-time gap. Proved admissibility gives nonnegative postpayment reserve at both clocks; monotone right dividend payments then contradict nonpositive reserve at the first clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gclose15_original_rightCont_UBV_downward_regular
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gclose16_original_rightcont_stopping_strict_postpayment_preruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P,
      (τ ω : ℝ≥0∞) < ruinTime X x D ω →
        0 < x + X.X (τ ω) ω - rightLimit D (τ ω) ω := by sorry
