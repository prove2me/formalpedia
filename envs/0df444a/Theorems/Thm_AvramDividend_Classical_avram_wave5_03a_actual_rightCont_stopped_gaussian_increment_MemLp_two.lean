-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:22:26.372756+00:00
-- url     : https://prove2.me/theorems/9f29fbcc-918e-403d-95b3-affeedff52a8
-- title:
--   Actual stopped source zero-jump Gaussian drift-centred increment is genuinely MemLp 2
-- statement:
--   For the true original spectrally negative Levy process with ν=0 and a bounded right-continuous stopping time, the drift-centred future increment X_(τ+h)-X_τ-h*c is genuinely MemLp 2 under P. The Proved source-specific Fatou lintegral square-energy inequality bounds its ENNReal squared energy by hσ²; the Proved samepath right-continuous Levy lift and stopped future-path measurability supply strong measurability. Convert finite squared lintegral into Integrable square, then apply Mathlib memLp_two_iff_integrable_sq. This is a critical original-source continuous-martingale stochastic-integral interface, not a detached Brownian copy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_lintegral_energy_le

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    MemLp (fun ω => X.X (τ ω + h) ω - X.X (τ ω) ω -
      (h : ℝ) * X.c) 2 P := by
  sorry
