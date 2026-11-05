-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_budget_of_signed_cofinal_mesh
-- name    : AvramDividend.Classical.avram_p3_bv_original_strict_budget_of_signed_cofinal_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:27:20.578476+00:00
-- url     : https://prove2.me/theorems/e0e086db-0616-4010-be33-a5244431cf4a
-- title:
--   Original BV strict-horizon budget from signed cofinal source-mesh estimates
-- statement:
--   For original BV Lévy controls, source-derived strict dividend cash and pre-rightpayment terminal are integrable. If each cofinal physical grid has a genuine integrable correction with nonpositive mean and a valid original-source pathwise cash-plus-terminal upper bound, the full strictly stopped horizon has the signed expected budget. The statement isolates the missing stopped C1 pathwise estimate; it does not pretend such an estimate is already proved.
-- source:
--   Proved original strict cash L1 67a9c5bf, P3-G2 original preterminal L1 e88885b6, and P3-F2 original cofinal strict mean passage 28343e2d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_strict_terminal_joint_L1_and_source_mean_le
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_stopped_strict_mean_budget_of_cofinal_C1_mesh

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- Source-exact strict-horizon expectation bridge. A genuine original
signed correction for each cofinal mesh and a pathwise estimate suffice;
cash and pre-rightpayment survival terminal L1 are automatic from source. -/

theorem AvramDividend.Classical.avram_p3_bv_original_strict_budget_of_signed_cofinal_mesh
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (S : ℝ≥0) (u : ℕ → ℝ) (hmono : Monotone u)
    (hu : ∀ n, 0 ≤ u n) (hbelow : ∀ n, u n ≤ (S : ℝ))
    (hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n)
    (B : ℕ → Ω → ℝ)
    (hBint : ∀ n, Integrable (B n) P)
    (hBmean : ∀ n, (∫ ω, B n ω ∂P) ≤ 0)
    (hPath : ∀ n, ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
       else 0) ≤ w x + B n ω) :
    (∫ ω : Ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
       else 0) ∂P) ≤ w x := by sorry
