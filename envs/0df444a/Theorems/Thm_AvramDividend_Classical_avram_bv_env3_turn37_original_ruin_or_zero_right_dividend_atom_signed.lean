-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn37_original_ruin_or_zero_right_dividend_atom_signed
-- name    : AvramDividend.Classical.avram_bv_env3_turn37_original_ruin_or_zero_right_dividend_atom_signed
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:40:52.769761+00:00
-- url     : https://prove2.me/theorems/5945e992-820a-4f9f-aff2-c93dbb12037d
-- title:
--   Original stopped pre-ruin and time-zero dividend atoms obey discounted signed BV bound
-- statement:
--   On the original controlled risk process with actual right-limit dividend strategy D, every pre-ruin right-payment atom, including the special time-zero atom, contributes nonpositively to discounted dividend cash plus postpayment value when the canonical payment-jump secant hypothesis holds. Exact source identity, no equality in law and no exclusion of the zero clock.
-- source:
--   BV-ENV3 original stopped BV Ito chain jump-atom sign, reduction of signed drift complement.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn37_original_ruin_or_zero_right_dividend_atom_signed
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (q : ℝ) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      Real.exp (-(q * (t : ℝ))) *
        ((rightLimit D t ω - D t ω) +
         w (riskProcess X x D t ω -
           (rightLimit D t ω - D t ω)) -
         w (riskProcess X x D t ω)) ≤ 0 := by sorry
