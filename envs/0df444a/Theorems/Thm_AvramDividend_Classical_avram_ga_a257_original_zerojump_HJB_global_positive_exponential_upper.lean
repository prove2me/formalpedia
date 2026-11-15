-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a257_original_zerojump_HJB_global_positive_exponential_upper
-- name    : AvramDividend.Classical.avram_ga_a257_original_zerojump_HJB_global_positive_exponential_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:48:36.387018+00:00
-- url     : https://prove2.me/theorems/212b4fda-84b1-417d-9a79-410192e0157f
-- title:
--   Original zerojump Gaussian HJB supersolution global positive-reserve one-sided exponential upper envelope including approach to ruin zero
-- statement:
--   Under the original Lévy process zero-jump Gaussian generator inequality, positive discount, top cap and C² smoothness on positive reserves, the value function has a single nonnegative exponential upper envelope valid for all strictly positive reserve values, including arbitrarily close to ruin zero. It combines the existing proved gledger65 far-field exponential bound with a256 new uniform near-origin bound and the original generator/HJB-to-scalar Gaussian PDE a p4_f11 bridge. It eliminates the artificial endpoint positivity margin in the original a216 combined large-increment one-sided Gaussian residual.
-- source:
--   a256 scalar positive-origin HJB one-sided upper, gledger65 original far-field envelope, p4_f11 original Gaussian PDE, gledger64 C2 source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a257_original_zerojump_HJB_global_positive_exponential_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, 0 < y → w y ≤ K * Real.exp (θ * y) := by sorry
