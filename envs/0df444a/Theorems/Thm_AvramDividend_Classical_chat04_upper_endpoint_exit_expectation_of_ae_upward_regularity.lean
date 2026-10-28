-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_exit_expectation_of_ae_upward_regularity
-- name    : AvramDividend.Classical.chat04_upper_endpoint_exit_expectation_of_ae_upward_regularity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:56:07.550394+00:00
-- url     : https://prove2.me/theorems/bf738dc2-2e7d-4823-9f6c-9e27fb2c3cf9
-- title:
--   Upper-reserve two-sided exit discount equals one under upward regularity alone
-- statement:
--   At starting reserve x=a with a>0, the strict downward passage cannot occur instantaneously because the Lévy path starts at zero and is right-continuous. Thus the only remaining condition for the upper-before-ruin discounted exit expectation to equal one is almost-sure upward regularity: arbitrarily small positive times at which X_t>0. This is a direct boundary case of the parent two-sided-exit identity.
-- source:
--   Composes Proved chat04_upper_endpoint_exit_expectation_of_ae_regular_windows 3bdb260e-3431-4b7c-a303-22490db7e53a, pending chat04_initial_safe_window_of_rightCont_zero 7c9b8b20-5b1b-4f1d-8e2e-979243bf3747 and built-in X.X_zero, in the import chain towards two_sided_exit_before_ruin_integral_identity 3e1ce2c8.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_exit_expectation_of_ae_regular_windows
import Theorems.Thm_AvramDividend_Classical_chat04_initial_safe_window_of_rightCont_zero

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_upper_endpoint_exit_expectation_of_ae_upward_regularity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a : ℝ) (ha : 0 < a)
    (hplus : ∀ᵐ ω ∂P,
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω) :
    twoSidedExitExpectation X q a a = 1 := by sorry
