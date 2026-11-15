-- Prove2me | Theorems.Thm_APFPaper5_K1_sharedCost_familyCost_nonneg_of_join
-- name    : APFPaper5.K1.sharedCost_familyCost_nonneg_of_join
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:14:14.423209+00:00
-- url     : https://prove2.me/theorems/460a068a-6cf9-48f8-8840-89338380f166
-- title:
--   For feasible families with admissible union, the capacity-limited bill-bounded join clause implies nonnegative shared cost
-- statement:
--   For feasible families with admissible union, the capacity-limited bill-bounded join clause implies nonnegative shared cost.
-- source:
--   Paper 1 Supplement v9.28:1313-1322,1761-1766,1774-1885,2624-2625,2777-2782,7101

import Definitions.Def_APFPaper1_FamilyCost
import Theorems.Thm_APFPaper5_K1_sharedCost_self
import Theorems.Thm_APFPaper5_K1_sharedCost_le_right
import Theorems.Thm_APFPaper5_K1_sharedCost_le_left
import Theorems.Thm_APFPaper5_K1_sharedCost_nonneg_iff
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_ledger
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_no_joint
import Theorems.Thm_APFPaper5_K1_cost_is_count_times_floor
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace APFPaper1.Source
end APFPaper1.Source
open APFPaper1.Source

open APFPaper1.Source in
theorem APFPaper5.K1.sharedCost_familyCost_nonneg_of_join {D P R Record : Type*} [DecidableEq D]
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (C : ℝ) (S T : Finset D)
    (hS : familyFeasible maintained sufficient usesToRealize S)
    (hT : familyFeasible maintained sufficient usesToRealize T)
    (hU : familyAdmissible wholeResource calibration maintained sufficient usesToRealize C (S ∪ T))
    (hjoin : ∀ p q : P,
      (∀ d ∈ S, ∃ sigma : Set Record,
        sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) →
      (∀ d ∈ T, ∃ sigma : Set Record,
        sigma ⊆ maintained q ∧ sufficient q sigma d ∧ usesToRealize q d sigma) →
      (calibration (wholeResource p) : ℝ) + (calibration (wholeResource q) : ℝ) ≤ C →
      ∃ pq : P,
        (∀ d ∈ S ∪ T, ∃ sigma : Set Record,
          sigma ⊆ maintained pq ∧ sufficient pq sigma d ∧ usesToRealize pq d sigma) ∧
        (calibration (wholeResource pq) : ℝ) ≤
          (calibration (wholeResource p) : ℝ) + (calibration (wholeResource q) : ℝ)) :
    0 ≤ APFPaper5.K1.sharedCost
      (familyCost wholeResource calibration maintained sufficient usesToRealize) S T := by sorry
