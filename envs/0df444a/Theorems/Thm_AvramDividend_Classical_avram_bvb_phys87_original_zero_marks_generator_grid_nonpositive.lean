-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys87_original_zero_marks_generator_grid_nonpositive
-- name    : AvramDividend.Classical.avram_bvb_phys87_original_zero_marks_generator_grid_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T08:22:32.206213+00:00
-- url     : https://prove2.me/theorems/e99ddb0d-2a91-4a5b-95ce-16e1841f635d
-- title:
--   Original negative-mark-free BV weighted HJB generator grid is nonpositive
-- statement:
--   On the original same-probability Lévy space, the sign of an exact stopped weighted BV grid B transfers to the frozen generator grid G when the negative intrinsic jump-mark count is zero. The previously proved physical zero-remainder theorem eliminates the entire weighted residual.
-- source:
--   Original bounded-variation physical grid 4f605d76 and Proved phys81 ddecee05

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys87_original_zero_marks_generator_grid_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (T : ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0)
    (hu : ∀ n i, i ≤ n + 1 → u n i ≤ T)
    (W : ℕ → ℕ → Ω → ℝ)
    (B G : ℕ → Ω → ℝ)
    (hB : ∀ n ω, B n ω = G n ω +
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
       let R : ℝ≥0 → ℝ := fun t =>
         ((t : ℝ) * X.drift - X.X t ω) - J t
       ∑ i ∈ Finset.range (n + 1),
         W n i ω * (R (u n i) - R (u n (i + 1)))))
    (hAllB : ∀ᵐ ω ∂P, ∀ n : ℕ, B n ω ≤ 0) :
    ∀ᵐ ω ∂P,
      (((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧
        X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v ≠ 0}).map
        (fun v : ℝ≥0 => (v, X.X v ω - Function.leftLim
          (fun z : ℝ≥0 => X.X z ω) v)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0) →
      ∀ n : ℕ, G n ω ≤ 0  := by sorry
