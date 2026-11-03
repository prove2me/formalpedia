-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_gaussian_condExp_mean_variance
-- name    : AvramDividend.Classical.avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_gaussian_condExp_mean_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:04:30.258363+00:00
-- url     : https://prove2.me/theorems/6c29c7d8-3ea1-4409-a48d-a3dc949c219d
-- title:
--   Canonical Lévy X minus source jumps has stopped Gaussian conditional mean zero and sigma squared variance
-- statement:
--   For bounded stopping time tau of the canonical original spectrally negative Lévy filtration, and the pathwise Gaussian residual M_t := X.X_t - t X.c - Jsmall_t - Jlarge_t, the increment M_(tau+h)-M_tau is integrable with conditional mean zero given F_tau, its square is integrable and its conditional second moment is (h:Real)*X.sigma squared. The same-original-space zero-jump Gaussian process Y and source decomposition are explicit hypotheses, preserving original Omega/P/filtration. This supplies the exact stopped Gaussian martingale variance coefficient without changing the underlying sample space.
-- source:
--   Wave6 remote-Proved original right-continuous zerojump stopped Gaussian conditional mean-variance theorem UUID ee632d15-4ba9-47ec-acfd-165214fcc0c3, transferred by the explicit same-space hSourceDecomp pathwise identity.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_condExp_mean_variance

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_gaussian_condExp_mean_variance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω + Jlarge t ω)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let V : Ω → ℝ := fun ω =>
      M (τ ω + h) ω - M (τ ω) ω
    Integrable V P ∧
      (P[V | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ))) ∧
      Integrable (fun ω => V ω ^ 2) P ∧
      (P[(fun ω => V ω ^ 2) |
        (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (h : ℝ) * X.σ ^ 2)) := by sorry
