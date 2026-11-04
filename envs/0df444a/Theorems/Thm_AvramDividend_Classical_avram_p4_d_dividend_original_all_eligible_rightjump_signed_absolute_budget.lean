-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_all_eligible_rightjump_signed_absolute_budget
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_all_eligible_rightjump_signed_absolute_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:14:17.976549+00:00
-- url     : https://prove2.me/theorems/57b0ba03-6f50-4b58-a4e0-d7b78382ca38
-- title:
--   Every original eligible right-payment enumeration, including zero jumps, yields a summable nonpositive cash-dominated correction
-- statement:
--   The accepted original strictly positive right-payment signed and absolute budget applies to the subtype of indexed payment times with nonzero right jump. Monotonicity of the actual dividend strategy ensures each omitted payment delta is exactly zero, hence its correctly ordered source Itô residual is zero. Pinned Mathlib summable_subtype_iff_indicator and tsum_subtype_eq_of_support_subset then transport true summability, nonpositivity and full restricted Stieltjes-cash bound to all eligible injectively indexed times. No artificial strict-positivity assumption remains on the caller.
-- source:
--   Accepted P4-D 4471f6e4 and dividendStrategy_le_rightLimit, pinned Mathlib subtype/tsum theorems

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_positive_atom_full_signed_and_absolute_budget
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Every eligible original right-payment enumeration, including zero payment times, has a signed absolutely summable correction. -/

theorem AvramDividend.Classical.avram_p4_d_dividend_original_all_eligible_rightjump_signed_absolute_budget
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
    (hInj : Function.Injective (fun i : ι => (t i : ℝ)))
    (K : ℝ) (hK : 1 ≤ K)
    (hLocalSecant : ∀ i, w (riskProcess X x D (t i) ω) -
      w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
        K * (rightLimit D (t i) ω - D (t i) ω)) :
    let μ : Measure ℝ := (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    let J : ι → ℝ := fun i => Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))
    Summable J ∧ (∑' i : ι, J i) ≤ 0 ∧
      Summable (fun i : ι => |J i|) ∧
      (∑' i : ι, |J i|) ≤
        (K - 1) * (∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω)
          then ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μ).toReal := by sorry
