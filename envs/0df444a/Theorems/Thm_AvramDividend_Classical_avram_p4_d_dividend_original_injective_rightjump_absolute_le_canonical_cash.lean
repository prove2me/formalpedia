-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_injective_rightjump_absolute_le_canonical_cash
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_injective_rightjump_absolute_le_canonical_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:17:00.572635+00:00
-- url     : https://prove2.me/theorems/1421f332-bb45-4b4d-b5bf-646cc593dbc5
-- title:
--   Original countable right-payment correction absolutely bounded by exact canonical ruin-stopped Cash
-- statement:
--   The already proved corrected strong source-original countable atomic carrier supplies genuine absolute summability and a K−1 times complete restricted closed-horizon dividendMeasure envelope for every injective index family of true eligible right payments in the same carrier. The exact closed-restriction-to-canonical-cash identity replaces that bound without loss by the literal P4-F Cash integral over paymentTimes(ruinTime)∩Iic T against the original dividendMeasure. Thus all pre-ruin atoms, time zero, simultaneous original source/payment jumps and the surviving horizon right atom are handled, with every continuous or singular-continuous payment retained in the complete RHS Cash. The only analytic bound is the stated honest source-state local secant, whose derivation on compact interior strips is separately established, and the cap/zero contact case remains with P4-E.
-- source:
--   Accepted P4-D corrected 172ef26b and exact P4-D closed restriction cash bridge under publication; P4-F literal hCash; original Eq. (5.13)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_injective_true_rightjump_absolute_le_full_cash_strong_carrier
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_restrict_cash_eq_literal_stop
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_injective_rightjump_absolute_le_canonical_cash
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
    (K : ℝ) (hK : 1 ≤ K)
    (hLocalSecant : ∀ i, w (riskProcess X x D (t i) ω) -
      w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
        K * (rightLimit D (t i) ω - D (t i) ω)) :
    let μ : Measure ℝ := (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ A : Set ℝ, A.Countable ∧
      (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) ∧
      ((∀ i : ι, (t i : ℝ) ∈ A) →
      Function.Injective (fun i : ι => (t i : ℝ)) →
        Summable (fun i : ι => |Real.exp (-(q * (t i : ℝ))) *
          ((rightLimit D (t i) ω - D (t i) ω) +
            w (x + X.X (t i) ω - rightLimit D (t i) ω) -
            w (riskProcess X x D (t i) ω))|) ∧
        (∑' i : ι, |Real.exp (-(q * (t i : ℝ))) *
          ((rightLimit D (t i) ω - D (t i) ω) +
            w (x + X.X (t i) ω - rightLimit D (t i) ω) -
            w (riskProcess X x D (t i) ω))|) ≤
          (K - 1) *
          (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) := by sorry
