-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_discounted_interior_HJB_grid_nonpositive
-- name    : AvramDividend.Classical.avram_p3_bv_original_discounted_interior_HJB_grid_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:23:28.811204+00:00
-- url     : https://prove2.me/theorems/d5cb1c79-c8d3-4d5b-9843-e35ef0d35ede
-- title:
--   Discounted original Lévy generator HJB grid drift is nonpositive on strict interior cells
-- statement:
--   For every source-process finite increasing deterministic grid and any sample-dependent prestates, the discounted generator minus q-value term, multiplied by the nonnegative cell width and gated to the strict positive cap interior, is pathwise nonpositive. The proof uses the exact original generator integrability/HJB hypothesis on that interior; it assigns zero to zero and cap-contact cells, which must be accounted separately in the complete stopped budget.
-- source:
--   Original SpectrallyNegativeLevy.generator and GeneratorIntegrable definitions; hgen sign; positive discount and monotone grid

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- Original source HJB drift, discounted on finite grid cells: only strict
interior states contribute; zero and cap contact remain separately owned. -/

theorem AvramDividend.Classical.avram_p3_bv_original_discounted_interior_HJB_grid_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (q : ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (Z : ℕ → Ω → ℝ) :
    ∀ ω,
      (∑ i ∈ Finset.range n,
        if 0 < Z i ω ∧ ENNReal.ofReal (Z i ω) < C then
          Real.exp (-(q * (u i : ℝ))) *
            (X.generator w (Z i ω) - q * w (Z i ω)) *
            ((u (i + 1) : ℝ) - (u i : ℝ))
        else 0) ≤ 0 := by sorry
