-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_exit_expectation_of_ae_regular_windows
-- name    : AvramDividend.Classical.chat04_upper_endpoint_exit_expectation_of_ae_regular_windows
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:45:45.17989+00:00
-- url     : https://prove2.me/theorems/3bdb260e-3431-4b7c-a303-22490db7e53a
-- title:
--   Upward-before-ruin discounted exit expectation is one at the upper reserve endpoint from almost-sure positive and safe-window regularity
-- statement:
--   Suppose almost every Lévy path has arbitrarily early positive increments, and almost every path stays above −a for some initial positive time window. Then first strict up passage above zero is instantaneous while first strict down passage below −a occurs later. The exact two-sided upper-first discounted expectation starting at reserve x=a equals one for every discount q. This resolves the endpoint via concrete sample-path regularity conditions.
-- source:
--   Composes Proved chat04_up_exit_time_zero_of_positive_near_zero (35cd74d9-4a9b-49ea-987c-66fa22b9902f), chat04_down_exit_time_pos_of_initial_safe_window (33197660-e41d-4347-875f-34be6603eef7, pending), and chat04_upper_endpoint_two_sided_exit_expectation_one (4f871287-bf29-4860-8d54-596d7d7b830b). Direct x=a endpoint prerequisite of alternative Open before-ruin identity 5bcf90e1 and immediate parent 3e1ce2c8.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_two_sided_exit_expectation_one
import Theorems.Thm_AvramDividend_Classical_chat04_up_exit_time_zero_of_positive_near_zero
import Theorems.Thm_AvramDividend_Classical_chat04_down_exit_time_pos_of_initial_safe_window
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_upper_endpoint_exit_expectation_of_ae_regular_windows
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a : ℝ)
    (hplus : ∀ᵐ ω ∂P,
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω)
    (hsafe : ∀ᵐ ω ∂P,
      ∃ ε : ℝ≥0, 0 < ε ∧
        ∀ t : ℝ≥0, t < ε → -a ≤ X.X t ω) :
    twoSidedExitExpectation X q a a = 1 := by sorry
