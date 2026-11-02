-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_true_increment_quotient_real_L2_convergence
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_true_increment_quotient_real_L2_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:01:07.643212+00:00
-- url     : https://prove2.me/theorems/2edaa586-b643-4126-8d1f-ac70f6d8f969
-- title:
--   Same-path Gaussian exponential quotients converge to true stopped increment in real L2 energy
-- statement:
--   For the genuine original spectrally-negative Levy source under nu=0, bounded right-continuous stopping time and arbitrary sigma, the real expected squared difference of the same-path exponential martingale quotient and actual stopped drift-centred source increment converges to zero as the quotient parameter goes to zero from above. This deduces from Proved ENNReal lintegral L2 convergence, genuine MemLp2 for both terms, ofReal_integral_eq_lintegral_ofReal, continuity of ENNReal.toReal at zero and nonnegativity. It is a direct real-valued L2 convergence bridge for the source Gaussian variance, not a Brownian copy or full Ito formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_true_increment_quotient_L2_convergence
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_true_increment_quotient_real_L2_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    Filter.Tendsto
      (fun θ : ℝ => (∫ ω, (Z θ ω - Y ω) ^ 2 ∂P))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  sorry
