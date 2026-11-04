-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_injective_true_rightjump_absolute_le_full_cash_strong_carrier
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_injective_true_rightjump_absolute_le_full_cash_strong_carrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:22:38.087125+00:00
-- url     : https://prove2.me/theorems/172ef26b-6ee1-4cbb-8fab-b2021cb065e4
-- title:
--   Strong original stopped single-carrier absolute right-dividend correction dominated by all Stieltjes cash
-- statement:
--   Under the exact original stopped Stieltjes atom carrier from the source, the carrier is guaranteed countable and supports every nonzero stopped singleton. For any indexed actual eligible payment times lying injectively in that carrier, the authentic post-X/pre-D right-dividend signed correction is absolutely summable and its absolute tsum is at most (K−1) times the full real discounted stopped Stieltjes integral including singular-continuous mass. Parentheses ensure Countable and support remain unconditional conjuncts of the existential proposition; the prior unparenthesised authoring attempt ba1cdac9 is deliberately not used as an import.
-- source:
--   Accepted a867cb3c same-carrier true cash control and accepted 9174e536 right-dividend absolute cash envelope; source 0a519d31 original atom/diffuse decomposition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_injective_atomic_cash_full_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_cash_summable_implies_absolute_remainder_envelope
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_injective_true_rightjump_absolute_le_full_cash_strong_carrier
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
      w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤ K * (rightLimit D (t i) ω - D (t i) ω)) :
    let μ : Measure ℝ := (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ A : Set ℝ, A.Countable ∧
      (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) ∧
      ((∀ i : ι, (t i : ℝ) ∈ A) →
      Function.Injective (fun i : ι => (t i : ℝ)) →
        Summable (fun i : ι => |Real.exp (-(q * (t i : ℝ))) *
          ((rightLimit D (t i) ω - D (t i) ω) + w (x + X.X (t i) ω - rightLimit D (t i) ω) -
            w (riskProcess X x D (t i) ω))|) ∧
        (∑' i : ι, |Real.exp (-(q * (t i : ℝ))) *
          ((rightLimit D (t i) ω - D (t i) ω) + w (x + X.X (t i) ω - rightLimit D (t i) ω) -
            w (riskProcess X x D (t i) ω))|) ≤
          (K - 1) * (∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω)
            then ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μ).toReal) := by sorry
