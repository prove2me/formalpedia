-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_clipped_discounted_finitegrid_drift_control_nonpos
-- name    : AvramDividend.Classical.avram_p4_f3_original_clipped_discounted_finitegrid_drift_control_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:48:10.738774+00:00
-- url     : https://prove2.me/theorems/6594404b-736c-4658-a2a7-75dcca6ddb5e
-- title:
--   Original clipped discounted finite-grid HJB generator and dividend-control budget is nonpositive
-- statement:
--   For the actual stopped source reserve X controlled by D, all finite physical time-space tagged grids with nonnegative interval lengths have a nonpositive total discounted HJB generator plus continuous dividend-control drift. It follows by summing the pointwise genuine source HJB/control sign over the physical grid.
-- source:
--   Original clipped physical predividend reserve, pointwise established generator and control sign, and nonnegative physical grid cell lengths.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_clipped_HJB_with_nonnegative_dividend_rate
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_clipped_discounted_finitegrid_drift_control_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    (r : ℝ≥0 × Ω → ℝ) (hr : ∀ p, 0 ≤ r p)
    {ι : Type*} (s : Finset ι) (p : ι → ℝ≥0 × Ω)
    (Δ : ι → ℝ) (hΔ : ∀ i ∈ s, 0 ≤ Δ i) :
    let U : ℝ≥0 × Ω → ℝ := fun z =>
      let y := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t z.2 - rightLimit D t z.2) z.1
      if y ∈ Icc δ K then y else δ
    ∑ i ∈ s, Δ i *
      (Real.exp (-(q * ((p i).1 : ℝ))) *
        ((X.generator w (U (p i)) - q * w (U (p i))) +
          r (p i) * (1 - deriv w (U (p i))))) ≤ 0 := by sorry
