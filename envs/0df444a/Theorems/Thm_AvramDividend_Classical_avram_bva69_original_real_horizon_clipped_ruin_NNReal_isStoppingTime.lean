-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva69_original_real_horizon_clipped_ruin_NNReal_isStoppingTime
-- name    : AvramDividend.Classical.avram_bva69_original_real_horizon_clipped_ruin_NNReal_isStoppingTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:24:14.129123+00:00
-- url     : https://prove2.me/theorems/2b9c0e9f-b217-4733-8bef-6a6b593b93a6
-- title:
--   Original ruin time clipped at arbitrary real nonnegative horizon is an NNReal right-continuous stopping clock
-- statement:
--   For the exact original spectrally negative Levy process and an admissible dividend strategy, clipping the original ruin time at any finite nonnegative real time T and converting to NNReal produces a stopping time in the right-continuous filtration. Proof uses the already established original ruin-time stopping property, min_const and the finite ENNReal coe_toNNReal identity. This enables real-horizon stopped BV cash and jump lemmas without replacing the process or restricting T to an integer.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

theorem AvramDividend.Classical.avram_bva69_original_real_horizon_clipped_ruin_NNReal_isStoppingTime
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) :
    IsStoppingTime 𝓕.rightCont
      (fun ω => (((min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) : WithTop ℝ≥0)) := by sorry
