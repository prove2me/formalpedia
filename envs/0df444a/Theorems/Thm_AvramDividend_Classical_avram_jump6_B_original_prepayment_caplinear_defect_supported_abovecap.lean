-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_prepayment_caplinear_defect_supported_abovecap
-- name    : AvramDividend.Classical.avram_jump6_B_original_prepayment_caplinear_defect_supported_abovecap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:22:37.174836+00:00
-- url     : https://prove2.me/theorems/0f14a63f-0f53-4c82-8f16-d6707578e2be
-- title:
--   Original finitecap prepayment clipped-grid defect supported only above the cap
-- statement:
--   On the original Levy path and dividend strategy physical grid, the exact discounted caplinear V minus w prepayment defect has zero contributions whenever the original prepayment book is at most cap c. The remaining terms equal the linear-extension minus w overshoot above c, with no assumption about their sign or stochastic expectation. This localises the genuine outstanding finitecap source correction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_prepayment_caplinear_defect_supported_abovecap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c q : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (v : ℕ → ℝ≥0) (m : ℕ) (w V : ℝ → ℝ)
    (hV : ∀ z : ℝ, V z = if z ≤ c then w z else w c + (z - c)) :
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    (∑ i ∈ Finset.range m,
      Real.exp (-(q * (v (i + 1) : ℝ))) * (V (Z i) - w (Z i))) =
    (∑ i ∈ Finset.range m,
      if c < Z i then
        Real.exp (-(q * (v (i + 1) : ℝ))) *
          (w c + (Z i - c) - w (Z i))
      else 0) := by sorry
