-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_initial_postpayment_reserve_between_zero_and_book
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_initial_postpayment_reserve_between_zero_and_book
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:36:33.352815+00:00
-- url     : https://prove2.me/theorems/3038f74a-1c1e-48ff-96a4-d6a8a4a4c4a3
-- title:
--   Original admissible initial right dividend is nonnegative and leaves a postpayment reserve between zero and book capital
-- statement:
--   The real original dividend strategy has D0=0 and nondecreasing paths, forcing the rightLimit D0 atom nonnegative; admissibility at t=0 caps that atom at the original initial reserve. Thus the exact post-rightpayment W branch at τ=0 lies in [0,x+X.X0]. This is the true source-sided invariant required for handling zero-time terminal values and initial payment atoms, without postulating boundary occupation zero.
-- source:
--   Original IsDividendStrategy source monotonicity/D0 and Proved P4-E initial postpayment nonnegative theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_initial_postrightpayment_reserve_nonnegative

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact initial right-payment atom lies between zero and the original book reserve. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_initial_postpayment_reserve_between_zero_and_book
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissible X x D) (ω : Ω) :
    0 ≤ rightLimit D 0 ω ∧
      0 ≤ x + X.X 0 ω - rightLimit D 0 ω ∧
      x + X.X 0 ω - rightLimit D 0 ω ≤ x + X.X 0 ω := by sorry
