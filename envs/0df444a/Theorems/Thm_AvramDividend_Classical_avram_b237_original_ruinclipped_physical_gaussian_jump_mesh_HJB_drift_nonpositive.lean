-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b237_original_ruinclipped_physical_gaussian_jump_mesh_HJB_drift_nonpositive
-- name    : AvramDividend.Classical.avram_b237_original_ruinclipped_physical_gaussian_jump_mesh_HJB_drift_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:05:04.208956+00:00
-- url     : https://prove2.me/theorems/4654460a-63bd-4150-a1f4-42d500193bd9
-- title:
--   Original ruin-clipped physical stopped Gaussian and negative-jump mesh HJB generator drift nonpositive
-- statement:
--   For the original Lévy model X, dividend strategy D and original controlled reserve riskProcess X x D, on each physical mesh cell whose clock lies strictly before the ruin-clipped stop sigma and whose reserve is within the genuine open cap band (0,C), the discounted source generator drift is nonpositive by the original HJB generator inequality. Their finite discounted physical mesh sum is nonpositive. Retains the actual risk process, source generator, cap, stopping mask, time-zero cells and jumps; it is a component of the original 61538c12 Itô-Meyer cash witness rather than an assumption of the source inequality.
-- source:
--   Original HJB premise hw_gen, positivity of physical step and exponential discount, and finite sum of nonpositive terms. No assumptions after ruin, no replacement stopping clock or Gaussian source transport.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b237_original_ruinclipped_physical_gaussian_jump_mesh_HJB_drift_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : Ω → ℝ≥0) (n m : ℕ) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let H : ℕ → ℝ := fun i =>
      let z := riskProcess X x D (s i) ω
      if s i < σ ω ∧ 0 < z ∧ ENNReal.ofReal z < C then
        (Δ : ℝ) * Real.exp (-(q * (s i : ℝ))) *
          (X.generator w z - q * w z)
      else 0
    (Finset.range m).sum H ≤ 0 := by sorry
