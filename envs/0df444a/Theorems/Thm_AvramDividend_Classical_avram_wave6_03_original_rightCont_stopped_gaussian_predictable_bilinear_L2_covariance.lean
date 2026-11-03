-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_bilinear_L2_covariance
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_predictable_bilinear_L2_covariance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:19:05.962661+00:00
-- url     : https://prove2.me/theorems/d7cbcb91-15b4-46a1-8128-201cde0965cf
-- title:
--   Exact bilinear source stopped Gaussian L2 covariance for two bounded predictable weights
-- statement:
--   For the actual zero-jump spectrally negative Lévy source on its original Ω and right-continuous filtration, and any bounded right-continuous stopping time τ and horizon h, take two bounded stopped-history-measurable gradient-like coefficients G,H, also ambient measurable. The two actual source stochastic cells G(X_(τ+h)-X_τ-hc), H(X_(τ+h)-X_τ-hc) each belong to L²(P), and their bilinear covariance is exactly (h σ²) E[GH]. This is the polarised stochastic-integral isometry on the original X for arbitrary σ including σ=0, with no detached Brownian copy; it provides the cross-term control needed for an L² completion of same-source predictable simple stochastic integrals. It neither asserts continuity/bracket for a general jump-bearing source nor proves the complete Ito-Meyer formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_quadratic_energy_exact

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_predictable_bilinear_L2_covariance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (G H : Ω → ℝ)
    (hGstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] G)
    (hHstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hGglobal : Measurable G) (hHglobal : Measurable H)
    (BG BH : ℝ) (hBG : 0 ≤ BG) (hBH : 0 ≤ BH)
    (hGbound : ∀ ω, |G ω| ≤ BG)
    (hHbound : ∀ ω, |H ω| ≤ BH) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    MemLp (fun ω => G ω * Y ω) 2 P ∧
    MemLp (fun ω => H ω * Y ω) 2 P ∧
      (∫ ω, (G ω * Y ω) * (H ω * Y ω) ∂P) =
        (∫ ω, G ω * H ω ∂P) * ((h : ℝ) * X.σ ^ 2) := by
  sorry
