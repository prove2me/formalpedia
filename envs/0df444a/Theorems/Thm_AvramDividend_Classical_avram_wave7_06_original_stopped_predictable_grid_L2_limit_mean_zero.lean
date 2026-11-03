-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_stopped_predictable_grid_L2_limit_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_06_original_stopped_predictable_grid_L2_limit_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:52:21.683281+00:00
-- url     : https://prove2.me/theorems/be18fb93-f0b5-42ca-a158-5bf30e301dc4
-- title:
--   Stopped original predictable finite-grid martingale L2 limit preserves zero mean
-- statement:
--   For actual source X, probability P, original filtration, stopped weights 1_{i<τ} H_{k,i}, and concrete finite-grid centred increments, a Cauchy sequence of exactly represented L2(P) approximants converges to an L2(P) random variable with zero original expectation. Explicit source-past measurability and cell integrability give zero expectation of every approximation. The L2 limit supplies a rigorous L1 expectation passage; the unproved step for intrinsic small jumps remains showing the exact marked truncations satisfy the L2 Cauchy condition.
-- source:
--   W7-06 original stopped finite-grid martingale L²/L¹ convergence consumer W7-07/W7-08.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_stopped_predictable_grid_L2_limit_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ → ℕ) (s t : ℕ → ℕ → ℝ≥0)
    (H : ℕ → ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (hWPast : ∀ k, ∀ i ∈ Finset.range (n k),
      Measurable[𝓕 (s k i)]
        (fun ω => if i < τ ω then H k i ω else 0))
    (hWI : ∀ k, ∀ i ∈ Finset.range (n k),
      Integrable (fun ω => if i < τ ω then H k i ω else 0) P)
    (hXI : ∀ k, ∀ i ∈ Finset.range (n k),
      Integrable (X.X (t k i)) P)
    (hCellI : ∀ k, ∀ i ∈ Finset.range (n k), Integrable (fun ω =>
      (if i < τ ω then H k i ω else 0) *
        (X.X (s k i + t k i) ω - X.X (s k i) ω -
          (∫ η, X.X (t k i) η ∂P))) P)
    (M : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
    (hSource : ∀ k, (M k : Ω → ℝ) =ᵐ[P] fun ω =>
      ∑ i ∈ Finset.range (n k),
        (if i < τ ω then H k i ω else 0) *
          (X.X (s k i + t k i) ω - X.X (s k i) ω -
            (∫ η, X.X (t k i) η ∂P)))
    (hCauchy : CauchySeq M) :
    ∃ L : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto M Filter.atTop (𝓝 L) ∧
      (∫ ω, L ω ∂P) = 0 := by sorry
