-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_stieltjes_dividend_interior_gradient_nonpositive
-- name    : AvramDividend.Classical.avram_wave7_02_original_stieltjes_dividend_interior_gradient_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:16:37.086195+00:00
-- url     : https://prove2.me/theorems/f2c20057-64e1-4c84-afe6-7003b7e2912b
-- title:
--   Original physical Stieltjes dividend derivative correction is nonpositive on arbitrary strict HJB interior region
-- statement:
--   For actual original dividendMeasure D ω and controlled riskProcess X x D, every measurable strictly positive reserve subcap region has nonpositive integrated discounted (1-deriv w) Stieltjes correction under canonical gradient condition and genuine integrability. Handles diffuse, singular-continuous and any right-atomic masses satisfying the region condition; endpoint atoms outside it require separate jump bounds.
-- source:
--   Exact canonical weak HJB gradient sign, physical original dividendMeasure and riskProcess with no synthetic payment measure or changed process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_stieltjes_dividend_interior_gradient_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (ω : Ω) (A : Set ℝ) (hA : MeasurableSet A)
    (hregion : ∀ t ∈ A,
      0 < riskProcess X x D t.toNNReal ω ∧
      ENNReal.ofReal (riskProcess X x D t.toNNReal ω) < C)
    (hInt : IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t)) *
        (1 - deriv w (riskProcess X x D t.toNNReal ω)))
      A (dividendMeasure D ω)) :
    (∫ t in A, Real.exp (-(q * t)) *
      (1 - deriv w (riskProcess X x D t.toNNReal ω))
      ∂(dividendMeasure D ω)) ≤ 0 := by sorry
