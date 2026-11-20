-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_initial_rightdividend_zero_clock_cash_contact_nonpositive
-- name    : AvramDividend.Classical.avram_pj_workerC_initial_rightdividend_zero_clock_cash_contact_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:05:24.184081+00:00
-- url     : https://prove2.me/theorems/e04578ad-5bde-4759-ad35-2b2d27ffad0e
-- title:
--   Genuine time-zero Iic discounted dividend atom plus post-right-reserve w correction is nonpositive under original HJB jump inequality
-- statement:
--   When the genuine original ruinclipped stop tau is zero, the inclusive paymentTimes Iic cash is the initial right-dividend jump. Nonnegative right-dividend jump and the source hjump inequality imply this initial cash plus the corresponding post-right-payment w correction is at most w(prepayment reserve). This matches the time-zero term of the physical four-term discounted grid exactly and prevents its atom from being silently discarded.
-- source:
--   Public Proved 5514c6b0 original zero-clock Iic cash=initial right atom, dividendStrategy_le_rightLimit, source hjump time0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_zero_clock_real_cash_eq_initial_rightatom
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_initial_rightdividend_zero_clock_cash_contact_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)))
    (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (ω : Ω) (hZero : τ ω = 0) :
    Cash ω +
      w (riskProcess X x D 0 ω -
        (rightLimit D 0 ω - D 0 ω)) ≤
      w (riskProcess X x D 0 ω) := by sorry
