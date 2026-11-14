-- Prove2me | Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
-- name    : APFPaper5.K1.record_book_table_satisfies_K1
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:05:18.105133+00:00
-- url     : https://prove2.me/theorems/f5af9f15-e184-4fd6-bb0f-9acf64a703e2
-- title:
--   A record table with positive private atoms realizes two algebraic K1 predicates
-- statement:
--   Supply finite atom and mark sets, Boolean marks and real atom weights. Assume hw: all weights are nonnegative, and hsingle: each mark has a positive-weight atom carrying that mark alone. The weighted overlap table then defines a real-bilinear coefficient form whose diagonal is nonnegative and faithful with identity role exchange. These are the two displayed algebraic predicates. The theorem does not establish a physical record book, normalized state weights, exact operational reproduction or completion of the physical K1 obligation.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_record_book_table.lean:101; Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex, 3721-3749; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 3038-3041

import Definitions.Def_APFPaper5_K1_OrderedScore
import Definitions.Def_APFPaper5_K1_MarkTable
import Theorems.Thm_APFPaper5_K1_tableForm_symm
import Theorems.Thm_APFPaper5_K1_roleExchange_respects_null
import Theorems.Thm_APFPaper5_K1_interchangeable_posDef
import Theorems.Thm_APFPaper5_K1_tableForm_isBilinear
import Theorems.Thm_APFPaper5_K1_interchangeable_marks_satisfy_K1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
universe u v
variable {ι : Type u} [Fintype ι] {W : Type v} [Fintype W]

theorem APFPaper5.K1.record_book_table_satisfies_K1 [DecidableEq ι] (w : W → ℝ) (hw : ∀ a, 0 ≤ w a)
    (mark : ι → W → Bool)
    (hsingle : ∀ i, ∃ a, 0 < w a ∧ ∀ j, mark j a = decide (j = i)) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm (atomTable w mark)) ∧
      FaithfulNonnegDiagonal (tableForm (atomTable w mark)) (LinearEquiv.refl ℝ (ι → ℝ)) := by sorry
