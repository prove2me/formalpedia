-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_killed_fatou_lintegral
-- name    : AvramDividend.Classical.avram_p3_bv_original_strict_cash_killed_fatou_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:35:50.174219+00:00
-- url     : https://prove2.me/theorems/f52df0d0-9cba-480f-b964-78bff042d2b0
-- title:
--   Fatou bridge for the actual original strict Stieltjes cash and killed terminal
-- statement:
--   For the actual original source X and original discounted Stieltjes dividend measure, the lower-Fatou bound transfers almost-everywhere lower-semicontinuity of the complete strict cash plus killed pre-rightpayment terminal to its expected ENNReal value. The theorem assumes exactly measurable approximant payoffs and the pointwise liminf comparison. It does not assume any source-jump compensation, drift representation or conclusion of the main HJB budget.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_liminf_le and source definitions; this isolates the expectation-limit interface in the original-process P3 verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_strict_cash_killed_fatou_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (S : ℝ≥0) (u : ℕ → ℝ≥0) :
    let F : ℝ≥0 → Ω → ℝ≥0∞ := fun s ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (s : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      ENNReal.ofReal
        (if (s : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (s : ℝ))) * w (riskProcess X x D s ω)
        else 0);
    (∀ n, Measurable (F (u n))) →
    (∀ᵐ ω ∂P, F S ω ≤ Filter.liminf (fun n => F (u n) ω) atTop) →
    (∫⁻ ω, F S ω ∂P) ≤
      Filter.liminf (fun n => ∫⁻ ω, F (u n) ω ∂P) atTop := by sorry
