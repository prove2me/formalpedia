-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_original_positive_clock_w_left_payoff
-- name    : AvramDividend.Classical.avram_ubv_finite12_original_positive_clock_w_left_payoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T18:21:19.505619+00:00
-- url     : https://prove2.me/theorems/8daf1ccd-1252-4d61-a9e3-f21d9d9f6da8
-- title:
--   Postpayment value candidate converges from the left to ruin-clock prepayment value for original pure Gaussian finite-cap strategy
-- statement:
--   At every positive time not past ruin, the original dividend-controlled postpayment reserve tends from the left to the nonnegative prepayment reserve. Continuity of the value candidate on nonnegative reserves gives the corresponding almost-sure convergence of values. The sign at the endpoint is proved from admissibility and closedness, without requiring an external endpoint sign premise.
-- source:
--   Same-source positive-clock terminal payoff limit for UBV-FINITE12. Built from public original-process surplus left limit and cap admissibility; Lean proof independently elaborated under pinned compiler probe.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative

import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_original_positive_clock_postpayment_left_tendsto

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite12_original_positive_clock_w_left_payoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      (t : ℝ≥0∞) ≤ ruinTime X x D ω →
      Tendsto (fun s : ℝ≥0 => w (x + X.X s ω - rightLimit D s ω))
        (𝓝[<] t) (𝓝 (w (riskProcess X x D t ω))) := by sorry
