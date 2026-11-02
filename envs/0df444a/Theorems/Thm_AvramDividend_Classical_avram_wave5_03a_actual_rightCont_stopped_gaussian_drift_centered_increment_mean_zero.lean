-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_drift_centered_increment_mean_zero
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_drift_centered_increment_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:12:14.812244+00:00
-- url     : https://prove2.me/theorems/98136b73-da5e-47f8-96ec-e46c4f31f2f3
-- title:
--   True original zero-jump Gaussian stopped drift-centred increment has expectation zero
-- statement:
--   For the genuine original SpectrallyNegativeLevy P F, ν=0 and an arbitrary bounded right-continuous stopping time τ, the actual drift-centred stopped increment X(τ+h)-Xτ-hc has expectation zero. Proof uses canonically Proved MemLp 2 of the actual stopped increment, the new source-path shifted Fatou bound E[(Y+a)^2]≤hσ²+a² for each real a, and elementary quadratic shift: if E[Y] were nonzero a tailored shift would contradict the bound. This yields true Gaussian source-increment centering, without detached Brownian coupling, independent Gaussian copies, or assuming an Ito integral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_shifted_fatou_energy

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_drift_centered_increment_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    (∫ ω, X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c ∂P) = 0 := by
  sorry
