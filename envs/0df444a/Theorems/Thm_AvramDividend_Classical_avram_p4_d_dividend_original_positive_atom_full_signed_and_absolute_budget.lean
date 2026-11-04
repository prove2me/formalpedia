-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_positive_atom_full_signed_and_absolute_budget
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_positive_atom_full_signed_and_absolute_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:56:23.852067+00:00
-- url     : https://prove2.me/theorems/4471f6e4-a3b2-4863-b76c-b0269bc2c30d
-- title:
--   Genuine original strictly positive right-jump signed remainder is summable, nonpositive and cash dominated
-- statement:
--   For an injective enumeration of strictly positive eligible original right-dividend payments at the true stopped horizon, the accepted P4-D positive singleton atom theorem supplies absolute convergence and an explicit K−1 times complete Stieltjes Cash bound without assuming a separately selected carrier. Mathlib Summable.of_abs transfers convergence to the signed genuine post-Lévy/pre-dividend residual series J. The original source conditional rightjump secant and accepted pointwise HasSum.nonpos theorem then prove ∑J≤0. This is a single source-specific signed and absolute aggregation interface that preserves zero and surviving-horizon right atoms and simultaneous X/D jumps. It remains conditional only on the honest local secant and actual injective enumeration; no boundary derivative extension is asserted.
-- source:
--   Accepted 3b48689b positive original true atom cash; accepted source P4-D countable rightjump signed tsum; pinned Summable.of_abs

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_positive_rightjump_absolute_fullcash_no_carrier_premise
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_countable_rightjump_signed_tsum_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_positive_atom_full_signed_and_absolute_budget
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
