-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_comp10_original_strict_cash_positive_excess_L1_of_capped_gradient
-- name    : AvramDividend.Classical.avram_p3_comp10_original_strict_cash_positive_excess_L1_of_capped_gradient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:31:36.977972+00:00
-- url     : https://prove2.me/theorems/29e0559b-66c2-4de7-aee2-2394862f8976
-- title:
--   Genuine original stopped strict-cash positive compensated residual is L1 under Avram's canonical cap and gradient assumptions
-- statement:
--   For the unchanged original BV process, admissible dividend strategy, strict pre-ruin cash, surviving postpayment terminal, and any integrable compensated and signed source rows, the positive part of F-(w(x)+M+B) is integrable rowwise. The actual canonical gradient and cap hypotheses prove w(x)≥x≥0, repairing the over-broad 092f30d0 without inventing an IsFiniteMeasure instance.
-- source:
--   Proved 781581e9, Proved 63bcc60a and new Proved 25e3c213; exact original F.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_canonical_strict_prefix_integrable
import Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_C1_closed_cap_payoff_above_reserve
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp10_positivepart_L1_of_nonnegative_shift
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_comp10_original_strict_cash_positive_excess_L1_of_capped_gradient
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) (hq : 0 < q) (T : ℝ) (hT : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (M B : ℕ → Ω → ℝ)
    (hMI : ∀ n, Integrable (M n) P)
    (hBI : ∀ n, Integrable (B n) P) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)
    ∀ n, Integrable
      (fun ω => max (F n ω - (w x + (M n ω + B n ω))) 0) P := by sorry
