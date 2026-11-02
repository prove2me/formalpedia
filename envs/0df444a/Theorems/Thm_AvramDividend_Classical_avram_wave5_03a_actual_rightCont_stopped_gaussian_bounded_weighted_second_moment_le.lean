-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_second_moment_le
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_second_moment_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:09:40.55673+00:00
-- url     : https://prove2.me/theorems/52b8cd0e-72a1-43fd-a876-541c23c60d8c
-- title:
--   Exact original stopped Gaussian bounded-gradient second-moment upper bound
-- statement:
--   For the genuine original no-jump spectrally negative Levy source and any bounded right-continuously stopped random time tau, a globally strongly measurable random multiplier H bounded pointwise by a nonnegative K has true original source Gaussian stochastic cell second moment at most K squared times h sigma squared. Uses canonically Proved true original stopped source variance bound and physical MemLp 2 of both unweighted and weighted cells. This is an explicit source-coupled variance-convention L2 localisation estimate without a Brownian copy, with sigma zero giving a zero upper bound. It does not assume stopped-history measurability, so applies a fortiori to bounded predictable coefficients.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_real_variance_le
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_second_moment_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (H : Ω → ℝ) (hHmeas : StronglyMeasurable H)
    (K : ℝ) (hK : 0 ≤ K) (hHbound : ∀ ω, |H ω| ≤ K) :
    (∫ ω, (H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) ^ 2 ∂P) ≤
      K ^ 2 * ((h : ℝ) * X.σ ^ 2) := by
  sorry
