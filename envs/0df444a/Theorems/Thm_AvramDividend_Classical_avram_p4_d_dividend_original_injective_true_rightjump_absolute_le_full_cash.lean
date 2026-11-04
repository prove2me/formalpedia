-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_injective_true_rightjump_absolute_le_full_cash
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_injective_true_rightjump_absolute_le_full_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:08:14.262884+00:00
-- url     : https://prove2.me/theorems/ba1cdac9-fa65-4ff5-a5fd-874f3f9383b0
-- title:
--   Source-ordered indexed true dividend right-jump absolute correction dominated by complete original stopped Stieltjes cash
-- statement:
--   Uses one genuine original stopped Stieltjes countable atomic carrier and its source-proved injective subseries domination to discharge all physical cash summability assumptions of the accepted right-jump absolute correction lemma. The indexed positive right-payment times are embedded injectively into that actual carrier and kept in [0,T] and paymentTimes. Under explicit canonical hjump and true local secant bound K, the absolute signed original post-X/pre-D right-payment correction is dominated by (K-1) times the exact complete discounted stopped Stieltjes cash. The diffuse mass, including singular-continuous contributions, remains inside the latter upper bound; no cap/zero derivative hypothesis is added.
-- source:
--   Accepted a867cb3c one-carrier original source atom subseries cash≤full Stieltjes; accepted 9174e536 source atom cash→absolute rightjump envelope; Mathlib tsum_mul_left and monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_injective_atomic_cash_full_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_cash_summable_implies_absolute_remainder_envelope
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_injective_true_rightjump_absolute_le_full_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤
        w (riskProcess X x D s ω) -
        w (riskProcess X x D s ω -
          (rightLimit D s ω - D s ω)))
    (t : ι → ℝ≥0) (ω : Ω) (T : ℝ≥0)
    (hT : ∀ i, t i ≤ T)
    (hPre : ∀ i, t i = 0 ∨ (t i : ℝ≥0∞) < ruinTime X x D ω)
    (hPay : ∀ i, (t i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (K : ℝ) (hK : 1 ≤ K)
    (hLocalSecant : ∀ i,
      w (riskProcess X x D (t i) ω) -
        w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
          K * (rightLimit D (t i) ω - D (t i) ω)) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ A : Set ℝ, A.Countable ∧
      (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) ∧
      (∀ i : ι, (t i : ℝ) ∈ A) →
      Function.Injective (fun i : ι => (t i : ℝ)) →
        Summable (fun i : ι => |Real.exp (-(q * (t i : ℝ))) *
          ((rightLimit D (t i) ω - D (t i) ω) +
            w (x + X.X (t i) ω - rightLimit D (t i) ω) -
            w (riskProcess X x D (t i) ω))|) ∧
        (∑' i : ι, |Real.exp (-(q * (t i : ℝ))) *
          ((rightLimit D (t i) ω - D (t i) ω) +
            w (x + X.X (t i) ω - rightLimit D (t i) ω) -
            w (riskProcess X x D (t i) ω))|) ≤
          (K - 1) * (∫⁻ s : ℝ,
            (if s ∈ paymentTimes (ruinTime X x D ω)
              then ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μ).toReal := by sorry
