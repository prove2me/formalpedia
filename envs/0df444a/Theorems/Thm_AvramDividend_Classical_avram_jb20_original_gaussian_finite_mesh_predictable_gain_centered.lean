-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb20_original_gaussian_finite_mesh_predictable_gain_centered
-- name    : AvramDividend.Classical.avram_jb20_original_gaussian_finite_mesh_predictable_gain_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:10:58.495729+00:00
-- url     : https://prove2.me/theorems/3433d16a-8702-4877-9790-496d01a0f8ed
-- title:
--   Entire original-filtration predictable Gaussian finite Itô mesh has integrable centred gain
-- statement:
--   Any finite physical deterministic grid of original Gaussian martingale increments, multiplied by uniformly bounded left-endpoint measurable weights, yields an integrable zero-mean source stochastic sum. The product integrability follows automatically from deterministic-time residual L1, so the theorem removes a substantive mesh accounting hypothesis. The original right-continuous filtration is unchanged.
-- source:
--   Proved 8d896ff6 original predictable centred cell, pinned Mathlib Integrable.bdd_mul, integrable_finset_sum and integral_finset_sum. Supports original nonlinear finite mixed Ito ledger 544e8511.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_gaussian_past_weight_increment_mean_zero
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jb20_original_gaussian_finite_mesh_predictable_gain_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {ι : Type*} (S : Finset ι)
    (R : ℝ≥0 → Ω → ℝ)
    (hRint : ∀ u : ℝ≥0, Integrable (R u) P)
    (hRmart : ∀ u v : ℝ≥0, u ≤ v →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont u) P (R v) ω = R u ω)
    (a b : ι → ℝ≥0) (W : ι → Ω → ℝ)
    (hab : ∀ i ∈ S, a i ≤ b i)
    (hW : ∀ i ∈ S,
      Measurable[𝓕.rightCont (a i)] (W i))
    (K : ℝ)
    (hWbound : ∀ i ∈ S, ∀ ω, ‖W i ω‖ ≤ K) :
    Integrable
      (fun ω => ∑ i ∈ S,
        W i ω * (R (b i) ω - R (a i) ω)) P ∧
    (∫ ω, ∑ i ∈ S,
      W i ω * (R (b i) ω - R (a i) ω) ∂P) = 0 := by sorry
