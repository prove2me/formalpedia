-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_ruin_stopped_HJB_grid_nonpositive
-- name    : AvramDividend.Classical.avram_p3_bv_original_ruin_stopped_HJB_grid_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:45:37.631091+00:00
-- url     : https://prove2.me/theorems/c46be6b6-db01-45c8-961b-956515d9cca3
-- title:
--   Original ruin-stopped BV left-prestate discounted generator mesh has nonpositive sign
-- statement:
--   For the original controlled Lévy source, on any finite nondecreasing time grid, retain the HJB generator term only when the original left-before-dividend reserve is strictly within the HJB cap interval and the grid cell starts before genuine ruin. Every such discounted term times the nonnegative cell width is nonpositive; all other cells contribute zero. The theorem does not assume survival at the next grid point and so allows ruin-crossing cells; jump and terminal accounting remain separate.
-- source:
--   Original SpectrallyNegativeLevy and DividendStrategy definitions, actual pre-rightpayment leftLimit, interior generator HJB sign

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- Actual original left-prestate HJB cells are retained only on the strict
pre-ruin region and strict cap interior. On a cell that can cross ruin,
its left-prestate HJB sign is still nonpositive; the separate source
jump and killed-terminal accounting remains necessary. -/

theorem AvramDividend.Classical.avram_p3_bv_original_ruin_stopped_HJB_grid_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1)) :
    ∀ ω,
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u i)
      (∑ i ∈ Finset.range n,
        if (u i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u i : ℝ))) *
            (X.generator w (Z i) - q * w (Z i)) *
            ((u (i + 1) : ℝ) - (u i : ℝ))
        else 0) ≤ 0 := by sorry
