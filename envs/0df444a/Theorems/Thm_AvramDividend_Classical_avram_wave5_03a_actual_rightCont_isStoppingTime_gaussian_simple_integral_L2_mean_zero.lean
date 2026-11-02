-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_isStoppingTime_gaussian_simple_integral_L2_mean_zero
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_isStoppingTime_gaussian_simple_integral_L2_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:08:54.614886+00:00
-- url     : https://prove2.me/theorems/e75f283b-74a6-4cd4-881d-e8e1bfc270b6
-- title:
--   Original bounded right-continuous IsStoppingTime Gaussian stochastic cell is L2 and centred
-- statement:
--   For a genuine original spectrally negative Levy source X with ν=0 and any bounded finite random clock τ satisfying Mathlib's IsStoppingTime for the original right-continuous filtration, a bounded real stopped-history measurable H defines a true original source drift-centred Gaussian cell H·(X_(τ+h)−X_τ−hc), both MemLp 2 and expectation zero under original P. Convert IsStoppingTime to finite ≤-event measurability in the same filtration, transport its stopped sigma-algebra, and import the already proved original stopped-history simple Gaussian L2 and martingale-difference lemma. This exact public interface uses Chat 03's IsStoppingTime convention, allows σ=0, and does not assume Brownian representation or the chain rule.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_simple_integral_L2_mean_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_isStoppingTime_gaussian_simple_integral_L2_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[hτ.measurableSpace] H)
    (K : ℝ) (hK : 0 ≤ K) (hHbound : ∀ ω, |H ω| ≤ K) :
    MemLp (fun ω =>
      H ω * (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) 2 P ∧
    (∫ ω, H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ∂P) = 0 := by
  sorry
