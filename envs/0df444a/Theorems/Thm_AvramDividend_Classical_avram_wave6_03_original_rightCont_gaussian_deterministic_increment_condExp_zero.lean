-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:20:03.867541+00:00
-- url     : https://prove2.me/theorems/61f27325-99ae-4e4e-94f3-757ef1949bb2
-- title:
--   Actual original Gaussian increment is integrable and conditionally centred in right-continuous filtration
-- statement:
--   For the given original spectrally negative Levy process X on its original probability space and right-continuous filtration, assume the source jump measure is zero but do not assume sigma positive. For every deterministic 0<=s<=t, the genuine drift-centred increment X.X_t-X.X_s-(t-s)c is integrable and its conditional expectation given F.rightCont_s is zero almost surely. Use the Proved genuine bounded-stopped source Gaussian MemLp2 and mean-zero results at the constant stopping time s, and the Proved original right-continuous independent-increment theorem together with the pinned condExp_indep_eq. This is an authentic Gaussian martingale-difference identity for the given X and filtration, not a separately coupled Brownian motion, not a quadratic-variation bracket and not the general-jump Ito formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_indepIncrements_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_drift_centered_increment_mean_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (s t : ℝ≥0) (hst : s ≤ t) :
    let Y : Ω → ℝ := fun ω => X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
    Integrable Y P ∧
      (P[Y | 𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ))) := by
  sorry
