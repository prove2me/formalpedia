-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_finite_grid_martingale_L2_limit_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_06_original_finite_grid_martingale_L2_limit_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:44:33.179733+00:00
-- url     : https://prove2.me/theorems/a072b7c7-bdbe-44d5-87b0-003b9bc9717b
-- title:
--   Original predictable finite-grid L2 martingale limit has integrable zero expectation
-- statement:
--   A sequence of finite-grid scalar source X martingale approximants, each a finite sum of original-filtration predictable centred increments, has an actual zero-mean L2(P) limit when its exact L2(P) representatives are Cauchy. The hSource hypothesis identifies each L2 representative almost everywhere with the concrete original process finite-grid sum. The one-cell L1 theorem gives zero expectation for every grid; L2 expectation continuity transfers mean zero through the limit, with no separate uniform-integrability assumption.
-- source:
--   W7-06 original filtration finite-grid source martingale truncation convergence/expectation handoff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_finite_grid_martingale_L2_limit_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ → ℕ) (s t : ℕ → ℕ → ℝ≥0)
    (W : ℕ → ℕ → Ω → ℝ)
    (hWPast : ∀ k, ∀ i ∈ Finset.range (n k),
      Measurable[𝓕 (s k i)] (W k i))
    (hWI : ∀ k, ∀ i ∈ Finset.range (n k), Integrable (W k i) P)
    (hXI : ∀ k, ∀ i ∈ Finset.range (n k), Integrable (X.X (t k i)) P)
    (hCellI : ∀ k, ∀ i ∈ Finset.range (n k), Integrable (fun ω =>
      W k i ω * (X.X (s k i + t k i) ω - X.X (s k i) ω -
        (∫ η, X.X (t k i) η ∂P))) P)
    (M : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
    (hSource : ∀ k, (M k : Ω → ℝ) =ᵐ[P] fun ω =>
      ∑ i ∈ Finset.range (n k),
        W k i ω * (X.X (s k i + t k i) ω - X.X (s k i) ω -
          (∫ η, X.X (t k i) η ∂P)))
    (hCauchy : CauchySeq M) :
    ∃ L : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto M Filter.atTop (𝓝 L) ∧
      (∫ ω, L ω ∂P) = 0 := by sorry
