-- Prove2me | Theorems.Thm_APFPaper1_Source_familyCost_union_le_of_join
-- name    : APFPaper1.Source.familyCost_union_le_of_join
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:08:48.818324+00:00
-- url     : https://prove2.me/theorems/c1328856-036a-4f18-81dd-c6fb1f251b40
-- title:
--   Family cost union le of join
-- statement:
--   For feasible S and T, if each pair of serving protocols can be joined to serve their union with bill at most the sum, union cost is at most the sum of their infimal costs.
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

theorem APFPaper1.Source.familyCost_union_le_of_join {D P R Record : Type*} [DecidableEq D]
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (S T : Finset D)
    (hS : familyFeasible maintained sufficient usesToRealize S)
    (hT : familyFeasible maintained sufficient usesToRealize T)
    (hjoin : ∀ p q : P,
      (∀ d ∈ S, ∃ sigma : Set Record,
        sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) →
      (∀ d ∈ T, ∃ sigma : Set Record,
        sigma ⊆ maintained q ∧ sufficient q sigma d ∧ usesToRealize q d sigma) →
      ∃ pq : P,
        (∀ d ∈ S ∪ T, ∃ sigma : Set Record,
          sigma ⊆ maintained pq ∧ sufficient pq sigma d ∧ usesToRealize pq d sigma) ∧
        (calibration (wholeResource pq) : ℝ) ≤
          (calibration (wholeResource p) : ℝ) + (calibration (wholeResource q) : ℝ)) :
    familyCost wholeResource calibration maintained sufficient usesToRealize (S ∪ T) ≤
      familyCost wholeResource calibration maintained sufficient usesToRealize S +
        familyCost wholeResource calibration maintained sufficient usesToRealize T := by sorry
