-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_simultaneous_source_then_dividend_full_HJB_jump_nonpos
-- name    : AvramDividend.Classical.avram_wave7_02_original_simultaneous_source_then_dividend_full_HJB_jump_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:42:50.134248+00:00
-- url     : https://prove2.me/theorems/3b3dab58-d96a-4d5b-97f9-77f71ec8269b
-- title:
--   Original negative source jump then simultaneous right dividend atom has joint nonpositive HJB correction
-- statement:
--   For an actual original spectrally negative Levy negative source mark at time t, with pre-source cap reserve nonnegative, the weak C1 HJB candidate cannot increase when the true source jump occurs, including landing at zero or overshooting below zero. If the canonical eligible right dividend payment occurs at t (time zero or strictly before ruin), hjump then bounds that atom by the additional candidate value drop. Their chronological joint correction paymentAtom+w(postpayment)-w(presource) is nonpositive. Exact original Ω, X, riskProcess, ruinTime and rightLimit D are retained; the positive-time ruin instant is excluded from eligible payments.
-- source:
--   Proved original negative source mark weak C1 value monotonicity e76d604b, canonical hjump with exact ruin-time eligibility and original before/after dividend chronology.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_source_jump_weak_C1_value_monotone_all_crossings
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_simultaneous_source_then_dividend_full_HJB_jump_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ (ω : Ω) (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω)
    (hMark : X.X t ω ≤ Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)
    (hb : 0 ≤ x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω)
    (hbC : ENNReal.ofReal
      (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) ≤ C) :
    (rightLimit D t ω - D t ω) +
      w (riskProcess X x D t ω -
        (rightLimit D t ω - D t ω)) -
      w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) ≤ 0 := by sorry
