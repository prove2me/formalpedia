-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_controlled_prejump_cap_hessian_stronglyPredictable
-- name    : AvramDividend.Classical.avram_wave5_03a_controlled_prejump_cap_hessian_stronglyPredictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:14:19.07217+00:00
-- url     : https://prove2.me/theorems/90335d62-36ad-4ed9-ab8f-b8991ce37a87
-- title:
--   Actual original prepayment capped second HJB derivative is strongly predictable on the right-continuous source filtration
-- statement:
--   For every original SpectrallyNegativeLevy P F source with arbitrary jump measure and Gaussian scale, every adapted admissible dividend strategy D, and any C2 HJB test w on the exact positive ENNReal-capped interior, the process applying the zero-extended second derivative iteratedDeriv 2 w to the strict-prepayment left-limit surplus is strongly predictable relative to the original right-continuous filtration. Compose the Proved strongly predictable actual postpayment-reserve left-limit with the new measurable Hessian cap extension. This is the genuine Gaussian Hessian stochastic-integrand predictable interface; unlike pure Gaussian variance estimates it requires no nu=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_measurable_cap_interior_iteratedDeriv_two_zero_extension

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_controlled_prejump_cap_hessian_stronglyPredictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    IsStronglyPredictable 𝓕.rightCont
      (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0) := by
  sorry
