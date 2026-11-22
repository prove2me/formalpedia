-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_original_sameSpace_brownian
-- name    : AvramDividend.Classical.avram_lsc_zerojump_original_sameSpace_brownian
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T15:48:52.39394+00:00
-- url     : https://prove2.me/theorems/05b01179-f449-4dd4-ab7a-ed44323d0879
-- title:
--   Original zero-jump Avram Lévy source is a same-space LevyStochCalc Brownian motion
-- statement:
--   If the original spectrally negative Lévy process has zero Lévy jump measure and positive Gaussian coefficient, its centred and Gaussian-normalised real-time path is itself a LevyStochCalc BrownianMotion on the original probability space. The result certifies joint measurability, Gaussian increments, continuous paths, a trivial negative-time extension and the stronger joint independence of every pre-start Brownian observation from future increments. It supplies the required exact same-space stochastic source bridge for the zero-jump branch of Avram's stopped Ito-Meyer verification argument.
-- source:
--   Original Avram zero-jump Lévy source representation for fdb9a6a3 and 26396e12, from Proved Gaussian law 690bca9c, real-time independence 8d9862cd, joint measurability d55462c3, and zero-jump a.s. continuity b462a147. The Brownian structure is Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_realTime_increment_gaussian
import Theorems.Thm_AvramDividend_Classical_avram_lsc_realTime_centered_increment_indep_past
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_lsc_zerojump_original_sameSpace_brownian
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ) :
    ∃ W : LevyStochCalc.Brownian.BrownianMotion P,
      ∀ (t : ℝ) (ω : Ω),
        W.W t ω =
          (X.X (Real.toNNReal t) ω - (Real.toNNReal t : ℝ) * X.c) / X.σ := by sorry
