-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_joint_cofinal_small_error_closed_real_perpetual
-- name    : AvramDividend.Classical.avram_limit2_joint_cofinal_small_error_closed_real_perpetual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:06:35.523078+00:00
-- url     : https://prove2.me/theorems/7bb817b7-8987-4519-be75-016137b5bd24
-- title:
--   Joint cofinal horizon and arbitrarily small error yield original closed real perpetual cash bounds
-- statement:
--   For the genuine original dividend process, the deterministic real horizons T_k need not be monotone and the nonnegative errors need not converge globally. It suffices that for every cash horizon a and positive epsilon there exists one index k with T_k≥a and error_k≤epsilon. Original discounted cash on paymentTimes(ruinTime) intersect Iic (T k), plus arbitrary nonnegative terminal, has expected ENNReal budget ≤finite B+error_k. Each canonical integer horizon is included in such an epsilon-good T_k, hence all integer cash is ≤B by positive additive epsilon removal. The already Proved original integer closed/strict exhaustion and finite-value signed Stieltjes real L1 theorem give actual perpetual value and expected real payout identity, preserving time-zero and finite endpoint atoms.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_joint_cofinal_small_error_closed_real_perpetual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (T : ℕ → ℝ) (error : ℕ → ℝ≥0∞)
    (hGood : ∀ ε : ℝ≥0, 0 < ε → ∀ a : ℝ,
      ∃ k : ℕ, a ≤ T k ∧ error k ≤ (ε : ℝ≥0∞))
    (B : ℝ≥0∞) (hB : B < ⊤)
    (hBudget : ∀ k : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T k),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤ B + error k) :
    dividendValue X q x D ≤ B ∧
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
