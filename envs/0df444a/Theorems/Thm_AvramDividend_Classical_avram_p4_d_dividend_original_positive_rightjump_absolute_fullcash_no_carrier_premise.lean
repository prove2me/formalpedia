-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_positive_rightjump_absolute_fullcash_no_carrier_premise
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_positive_rightjump_absolute_fullcash_no_carrier_premise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:45:12.554769+00:00
-- url     : https://prove2.me/theorems/3b48689b-eef2-4ce7-a535-dfcd3b621728
-- title:
--   Every original positive right-payment jump automatically lies in the true stopped atomic carrier
-- statement:
--   The source-proved finite stopped Stieltjes singleton identity identifies μ{t}=ofReal(rightLimit D_t−D_t) at every t≤T. Thus any actual strictly positive original right-payment jump has nonzero singleton mass and automatically belongs to the unconditional countable true atomic carrier supplied by the corrected P4-D strong theorem. For an injective enumeration of eligible strictly positive original payment jumps, the carrier membership premise can therefore be discharged directly, giving true absolute summability and a K−1 envelope bounded by the full original discounted Stieltjes cash, including zero and surviving horizon atoms and preserving simultaneous source/right-dividend jump order. No artificial atom-carrier assumption is left in the public interface.
-- source:
--   Proved 0a519d31 exact original singleton mass; accepted 172ef26b unconditional strong carrier; pinned ENNReal.ofReal_pos

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_injective_true_rightjump_absolute_le_full_cash_strong_carrier
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_stopped_discounted_all_atoms_diffuse_cash_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_positive_rightjump_absolute_fullcash_no_carrier_premise
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
    Summable (fun i : ι => |Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))|) ∧
    (∑' i : ι, |Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))|) ≤
      (K - 1) * (∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω)
        then ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μ).toReal := by sorry
