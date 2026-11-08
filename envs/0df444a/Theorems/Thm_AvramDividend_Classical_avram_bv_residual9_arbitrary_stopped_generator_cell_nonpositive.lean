-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_arbitrary_stopped_generator_cell_nonpositive
-- name    : AvramDividend.Classical.avram_bv_residual9_arbitrary_stopped_generator_cell_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:44:38.194957+00:00
-- url     : https://prove2.me/theorems/d5742793-df5c-41e6-874a-14a4a857fbe9
-- title:
--   Each original stopped HJB generator cell is nonpositive on every monotone physical grid
-- statement:
--   Under the canonical pointwise original generator/HJB sign hypothesis, a stopped pre-ruin positive interior physical-grid cell is nonpositive for each sample and index. The factor from monotonicity is nonnegative, the exponential weight strictly positive, and the generator residual nonpositive. This remains valid even for nonuniform nonrefining grids, and isolates the honest deterministic HJB half of the exact B sum; the raw compensated residual and L1 issues are separate.
-- source:
--   BV-RESIDUAL9 original arbitrary stopped physical-grid source cell.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_arbitrary_stopped_generator_cell_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) :
    ∀ n i, i < n + 1 → ∀ ω,
      (let Z : ℕ → ℝ := fun j => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
       if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
           0 < Z i ∧ ENNReal.ofReal (Z i) < C then
         Real.exp (-(q * (u n i : ℝ))) *
           (X.generator w (Z i) - q * w (Z i)) *
           ((u n (i + 1) : ℝ) - (u n i : ℝ))
       else 0) ≤ 0 := by sorry
