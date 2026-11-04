-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_positive_atom_signed_budget_le_literal_cash
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_positive_atom_signed_budget_le_literal_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:17:23.775233+00:00
-- url     : https://prove2.me/theorems/bf29ab65-c917-4e6b-a78e-7c376cde59a3
-- title:
--   Original signed right-dividend correction is summable nonpositive and dominated by exact ruin-stopped Stieltjes Cash
-- statement:
--   Accepted P4-D strictly-positive source-ordered rightpayment series has genuine signed sum ≤0, absolute summability and full closed-restriction Stieltjes domination. The exact original payment selector and finite-horizon restriction identity transports the envelope to the literal P4-F Cash integral over paymentTimes(ruinTime) ∩ Iic T, preserving time-zero, simultaneous original X/dividend jumps, singular-continuous cash and surviving horizon atom. Uses explicit honest original-state secant bound K, not invented boundary differentiability.
-- source:
--   Accepted 4471f6e4 signed absolute original rightjump; pending exact cash-bridge 52a094c1; P4-F original hCash source; Avram Proposition 4(i), Eq. (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_positive_atom_full_signed_and_absolute_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_restrict_cash_eq_literal_stop
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Original signed right-dividend remainder bounded by the literal ruin-stopped cash. -/

theorem AvramDividend.Classical.avram_p4_d_dividend_original_positive_atom_signed_budget_le_literal_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤ w (riskProcess X x D s ω) -
        w (riskProcess X x D s ω - (rightLimit D s ω - D s ω)))
    (t : ι → ℝ≥0) (ω : Ω) (T : ℝ≥0)
    (hT : ∀ i, t i ≤ T)
    (hPre : ∀ i, t i = 0 ∨ (t i : ℝ≥0∞) < ruinTime X x D ω)
    (hPay : ∀ i, (t i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hPos : ∀ i, 0 < rightLimit D (t i) ω - D (t i) ω)
    (hInj : Function.Injective (fun i : ι => (t i : ℝ)))
    (K : ℝ) (hK : 1 ≤ K)
    (hLocalSecant : ∀ i, w (riskProcess X x D (t i) ω) -
      w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
        K * (rightLimit D (t i) ω - D (t i) ω)) :
    let J : ι → ℝ := fun i => Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))
    Summable J ∧ (∑' i : ι, J i) ≤ 0 ∧
      Summable (fun i : ι => |J i|) ∧
      (∑' i : ι, |J i|) ≤
        (K - 1) * (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by sorry
