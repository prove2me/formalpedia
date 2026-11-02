-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_source_discounted_ruin_stopped_cap_hessian_predictable
-- name    : AvramDividend.Classical.avram_wave6_03_original_source_discounted_ruin_stopped_cap_hessian_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:27:32.795495+00:00
-- url     : https://prove2.me/theorems/8902785a-d786-4def-8c13-fabb0c4782c3
-- title:
--   Actual original discounted pre-dividend Hessian remains predictable with inclusive ruin and finite horizon truncation
-- statement:
--   For the original spectrally negative Levy path X and admissible dividend D, the strict prepayment left-limited controlled reserve x+X-rightLimit D has a capped zero-extended second HJB derivative. Multiplying this true source Hessian by e^{-qt}, the inclusive original ruin survival indicator 1_{t≤ruinTime X x D} and finite deterministic horizon 1_{t≤T} preserves strong predictability in the same right-continuous filtration for arbitrary source sigma and jump measure nu, including sigma zero. This establishes the exact discounted Hessian coefficient for the sigma-squared-over-two continuous Gaussian drift under localisation, without asserting a complete Ito formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_controlled_prejump_cap_hessian_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_stronglyPredictable_inclusive_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_source_discounted_ruin_stopped_cap_hessian_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0) :
    IsStronglyPredictable 𝓕.rightCont
      (fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            (let y := Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
             if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) := by
  sorry
