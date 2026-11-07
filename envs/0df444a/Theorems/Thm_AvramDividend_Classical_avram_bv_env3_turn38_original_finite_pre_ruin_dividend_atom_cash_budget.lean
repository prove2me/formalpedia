-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn38_original_finite_pre_ruin_dividend_atom_cash_budget
-- name    : AvramDividend.Classical.avram_bv_env3_turn38_original_finite_pre_ruin_dividend_atom_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:41:36.328488+00:00
-- url     : https://prove2.me/theorems/7ce44f7e-2dcc-427c-b3c5-cabb423fd85a
-- title:
--   Original finite-tagged pre-ruin and time-zero dividend atoms obey full cash-value budget
-- statement:
--   For any finite set of actual original dividend right-payment times contained in time zero or the strict pre-ruin interval, discounted right-limit dividend cash is bounded by the sum of genuine physical controlled-reserve value drops. The inequality retains time-zero and all selected pre-ruin atoms and makes no replacement of dividendMeasure by synthetic cash.
-- source:
--   BV-ENV3 source exact finite tagged Stieltjes cash jump accounting; helper toward stopped C1 Itô source identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn38_original_finite_pre_ruin_dividend_atom_cash_budget
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
    ∀ ω (F : Finset ℝ≥0),
      (∀ t ∈ F, t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      (∑ t ∈ F, Real.exp (-(q * (t : ℝ))) *
        (rightLimit D t ω - D t ω)) ≤
      (∑ t ∈ F, Real.exp (-(q * (t : ℝ))) *
        (w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))) := by sorry
