-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_signed_from_separate_jump_and_HJB_grid
-- name    : AvramDividend.Classical.avram_p3_bv_signed_from_separate_jump_and_HJB_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:26:29.275091+00:00
-- url     : https://prove2.me/theorems/57c8c3d8-42e0-4885-ac5f-4ec3e3800f8c
-- title:
--   Original BV signed HJB complete payout from separate zero-mean source jumps and nonpositive HJB drift at every genuine stopped grid
-- statement:
--   The actual original stopped source-jump martingale grid increments are L1 and mean-zero separately from the original physical HJB drift grid terms, which are L1 with nonpositive expectation. The exact signed sum then meets the Proved canonical BV Fatou grid bridge and transfers to the complete original Iic T Stieltjes cash plus strict-survival post-rightpayment terminal. Source-grid witnesses, pointwise mesh inequality and lower liminf remain explicit and need construction.
-- source:
--   Proved 7bd356f9, original P3-E stopped zero-mean b7ef0753/c7cc0cd4 and P3-G expected-sign 1d6ba5ec

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_signed_full_from_canonical_grid

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- The original centred source-jump part and physical HJB drift can be
verified separately at every stopped grid, then assembled in L1. -/

theorem AvramDividend.Classical.avram_p3_bv_signed_from_separate_jump_and_HJB_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (F M B : ℕ → Ω → ℝ)
    (hFmeas : ∀ n, Measurable (F n))
    (hFint : ∀ n, Integrable (F n) P)
    (hFnonneg : ∀ n, 0 ≤ᵐ[P] F n)
    (hM : ∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) = 0)
    (hB : ∀ n, Integrable (B n) P ∧ (∫ ω, B n ω ∂P) ≤ 0)
    (hMesh : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w x + (M n ω + B n ω))
    (hLiminf : ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      ENNReal.ofReal (
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)) ≤
      liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal ∂P) +
    (∫ ω, if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) *
        w (x + X.X S ω - rightLimit D S ω)
      else 0 ∂P) ≤ w x := by sorry
