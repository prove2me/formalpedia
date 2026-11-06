-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_clipped_discounted_slope_defect_nonpos
-- name    : AvramDividend.Classical.avram_p4_f3_original_clipped_discounted_slope_defect_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:34:22.736873+00:00
-- url     : https://prove2.me/theorems/ca395242-4a25-4402-b024-16c725235d23
-- title:
--   Actual original discounted clipped derivative slope deficit has nonpositive dividend sign
-- statement:
--   For the original predividend reserve of the physical spectrally negative Lévy X controlled by D, clipping to a strictly positive compact interior ensures the discounted first-derivative slope deficit is pointwise nonpositive. This is the continuous dividend-control Itô remainder sign for the actual source path.
-- source:
--   Direct original physical reserve clipping δ≤U≤K<C, standing slope bound deriv w≥1, and positive discount; no proxy processes or stochastic hypotheses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_clipped_discounted_slope_defect_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (q : ℝ)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    ∀ p : ℝ≥0 × Ω,
      Real.exp (-(q * (p.1 : ℝ))) *
        (1 - deriv w (U p)) ≤ 0 := by sorry
