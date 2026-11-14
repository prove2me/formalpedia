-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a60_original_BV_surviving_prepayment_dominates_afterpay_plus_right_dividend
-- name    : AvramDividend.Classical.avram_bva_a60_original_BV_surviving_prepayment_dominates_afterpay_plus_right_dividend
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T18:24:36.578228+00:00
-- url     : https://prove2.me/theorems/b425855d-35ac-43e0-8ffd-02fe4f168d14
-- title:
--   Original BV surviving horizon prepayment reward dominates postpayment reward plus horizon right dividend
-- statement:
--   For the actual original bounded-variation spectrally negative Lévy and admissible controlled dividends with potentially infinitely many negative jump times, prove the exact algebraic identity between the controlled reserve immediately before and after a permitted right dividend payment at a strictly surviving horizon, and prove that the original discounted prepayment candidate value dominates the discounted postpayment candidate value plus that dividend atom. This directly resolves the direction of the terminal-payment mismatch found in A58; it does not impose the incorrect equality between prepayment and postpayment values and does not replace the stopped stochastic source budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a60_original_BV_surviving_prepayment_dominates_afterpay_plus_right_dividend
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (q x : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ≥0) (ω : Ω)
    (hSurv : (T : ℝ≥0∞) < ruinTime X x D ω) :
    (x + X.X T ω - rightLimit D T ω =
      riskProcess X x D T ω -
        (rightLimit D T ω - D T ω)) ∧
    (Real.exp (-(q * (T : ℝ))) *
      (w (x + X.X T ω - rightLimit D T ω) +
        (rightLimit D T ω - D T ω)) ≤
      Real.exp (-(q * (T : ℝ))) *
        w (riskProcess X x D T ω)) := by sorry
