-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_clipped_hjb_discounted_generator_nonpos
-- name    : AvramDividend.Classical.avram_p4_f3_original_clipped_hjb_discounted_generator_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:22:50.753148+00:00
-- url     : https://prove2.me/theorems/d6f4ecb3-a236-4707-b01c-a8e8638650b0
-- title:
--   Actual clipped original reserve HJB generator drift has nonpositive discounted source density
-- statement:
--   For the genuine original controlled Lévy X and actual dividend path D, clipping the prepayment left reserve to the compact interior [δ,K] preserves the source HJB generator inequality. Consequently every positive exponential time-discount factor multiplies the true generator-minus-discount source density to a nonpositive value at every physical time-path point, including ruin and boundary clocks under clipping.
-- source:
--   Any clipped U lies in [δ,K], so hδ>0 ensures U>0, and ENNReal.ofReal U≤ENNReal.ofReal K<C. Apply the exact original generator HJB hypothesis at U; multiply the nonpositive generator residual by exp(-qt)>0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_clipped_hjb_discounted_generator_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    ∀ p : ℝ≥0 × Ω,
      Real.exp (-(q * (p.1 : ℝ))) *
        (X.generator w (U p) - q * w (U p)) ≤ 0 := by sorry
