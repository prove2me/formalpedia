-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger117_original_initial_contact_plus_dividend_atom_nonpositive
-- name    : AvramDividend.Classical.avram_gledger117_original_initial_contact_plus_dividend_atom_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T14:24:53.670209+00:00
-- url     : https://prove2.me/theorems/6888e48b-ba31-41e1-930d-f4c15068025b
-- title:
--   Original initial contact loss cancels the exact real dividend-measure atom
-- statement:
--   For the original admissible strategy, the loss in the candidate reward at the time-zero right dividend jump compensates the exact initial mass of its Stieltjes dividend measure. This supplies the zero-atom estimate for the gledger81 stopped dividend-contact budget. Nonnegativity and zero initial value of the strategy are explicit for direct reuse.
-- source:
--   Exact initial paid cash atom for root-connected original top-cap Gaussian contact ledger gledger81.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger117_original_initial_contact_plus_dividend_atom_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (hD0 : D 0 ω = 0) (hRight : 0 ≤ rightLimit D 0 ω) :
    (w (x - rightLimit D 0 ω) - w x) +
      (dividendMeasure D ω ({0} : Set ℝ)).toReal ≤ 0 := by sorry
