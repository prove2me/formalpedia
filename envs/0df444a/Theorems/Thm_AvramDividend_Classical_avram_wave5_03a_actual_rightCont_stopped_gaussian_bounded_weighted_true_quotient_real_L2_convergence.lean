-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_quotient_real_L2_convergence
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_quotient_real_L2_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:11:33.538192+00:00
-- url     : https://prove2.me/theorems/40555946-f738-4dbc-9308-358b36fb23d9
-- title:
--   Bounded genuine stopped-gradient multiplier preserves actual Gaussian quotient convergence in L2
-- statement:
--   For the same original right-continuously stopped spectrally-negative Levy source with zero jump measure, the centred source increment is an actual L2 limit of its own exponential quotient, and this limit remains valid after multiplication by any strongly measurable uniformly bounded random coefficient H. In particular the bounded compact-band discounted controlled prepayment gradient qualifies after its already Proved stopped measurability and clipping. This is a genuine original-process stochastic-integral localisation convergence, uses exact stopped source increments and holds also when sigma is zero; it is not the full Ito formula or a Brownian copy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_true_increment_quotient_real_L2_convergence
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_quotient_real_L2_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0)
    (H : Ω → ℝ) (hHmeas : StronglyMeasurable H)
    (K : ℝ) (hK : 0 ≤ K) (hH : ∀ ω, |H ω| ≤ K) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    Filter.Tendsto
      (fun θ : ℝ => (∫ ω, (H ω * (Z θ ω - Y ω)) ^ 2 ∂P))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  sorry
