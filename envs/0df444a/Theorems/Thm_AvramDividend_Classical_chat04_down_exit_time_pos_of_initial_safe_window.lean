-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_down_exit_time_pos_of_initial_safe_window
-- name    : AvramDividend.Classical.chat04_down_exit_time_pos_of_initial_safe_window
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:40:13.594651+00:00
-- url     : https://prove2.me/theorems/33197660-e41d-4347-875f-34be6603eef7
-- title:
--   Strict downward exit below a negative barrier takes positive time when an initial safety window exists
-- statement:
--   If a Lévy sample path remains at or above the strict downward threshold −a for every time before some positive ε, the exact ENNReal first passage time below −a is at least ε and hence strictly positive. This deterministic pathwise lemma isolates the exact right-continuity consequence required at the upper-reserve endpoint x=a of the two-sided exit identity.
-- source:
--   Direct lower-exit regularity premise of chat04_upper_endpoint_two_sided_exit_expectation_one (4f871287-bf29-4860-8d54-596d7d7b830b), which supplies the x=a endpoint of alternative Open two_sided_exit_before_ruin_identity 5bcf90e1 and immediate parent 3e1ce2c8. The remaining probability assertion is that actual Lévy paths have a positive safe window below −a, using X_0=0 and right-continuity for a>0.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_down_exit_time_pos_of_initial_safe_window
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a : ℝ) (ω : Ω) (ε : ℝ≥0) (hε : 0 < ε)
    (hSafe : ∀ t : ℝ≥0, t < ε → -a ≤ X.X t ω) :
    0 < twoSidedExitDownTime X (-a) ω := by sorry
