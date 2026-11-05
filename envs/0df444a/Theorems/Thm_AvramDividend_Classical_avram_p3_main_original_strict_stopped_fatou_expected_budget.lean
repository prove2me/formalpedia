-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_strict_stopped_fatou_expected_budget
-- name    : AvramDividend.Classical.avram_p3_main_original_strict_stopped_fatou_expected_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:47:15.370259+00:00
-- url     : https://prove2.me/theorems/5591152f-9a2e-42c0-8478-fe170d75b5b4
-- title:
--   Original bounded-variation strict-horizon expected HJB budget from localised Fatou liminf
-- statement:
--   For the genuine original Lévy process, admissible dividend strategy, strict-before-T Stieltjes cash and killed pre-rightpayment terminal, obtain the canonical real expected HJB bound from nonnegative measurable localised ENNReal payoffs whose almost-sure liminf dominates the exact stopped payoff and whose expectations are bounded by w(x). The source-exact integrability is supplied by the already-Proved original prebudget L1 theorem. This is the final Fatou expectation passage once the genuine stopped C1 and jump compensation estimates establish its two explicit localised premises.
-- source:
--   Original prebudget L1 78fa7075; exact strict paymentTimes and ruinTime definitions; pinned Mathlib lintegral_liminf_le and ofReal_integral_eq_lintegral_ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_main_original_strict_stopped_fatou_expected_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hwx : 0 ≤ w x)
    (F : ℕ → Ω → ℝ≥0∞) (hFmeas : ∀ n, Measurable (F n))
    (hLiminf : ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      ENNReal.ofReal (
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) *
            w (riskProcess X x D S ω)
        else 0)) ≤ liminf (fun n => F n ω) atTop)
    (hBudget : ∀ n,
      (∫⁻ ω, F n ω ∂P) ≤ ENNReal.ofReal (w x)) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ∂P) ≤ w x := by sorry
