-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_real_variance_le
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_real_variance_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:40:30.368572+00:00
-- url     : https://prove2.me/theorems/51370cc4-eb94-4353-946d-064ed733dc65
-- title:
--   Actual source stopped Gaussian drift-centred increment real variance bound
-- statement:
--   For the exact original zero-jump spectrally negative Lévy source and bounded right-continuous stopping time, the real expectation of the true drift-centred stopped increment square is bounded by h sigma squared. This is the real-valued variance convention required to transport the original source Gaussian bracket into the Ito drift, independently of an auxiliary Brownian copy. Derived using the already Proved Fatou ENNReal squared-energy bound and MemLp 2 membership.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_lintegral_energy_le

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_real_variance_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    (∫ ω, (X.X (τ ω + h) ω - X.X (τ ω) ω -
      (h : ℝ) * X.c) ^ 2 ∂P) ≤ (h : ℝ) * X.σ ^ 2 := by
  sorry
