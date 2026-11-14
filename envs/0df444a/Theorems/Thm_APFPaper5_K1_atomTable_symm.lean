-- Prove2me | Theorems.Thm_APFPaper5_K1_atomTable_symm
-- name    : APFPaper5.K1.atomTable_symm
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:05:02.032204+00:00
-- url     : https://prove2.me/theorems/13aee39d-4a39-4369-adc9-1b5b8d9550c6
-- title:
--   Weighted Boolean overlap tables are symmetric
-- statement:
--   For a finite atom set, arbitrary real weights w and Boolean marks mᵢ, define G(i,j)=Σₐwₐ[mᵢ(a)][mⱼ(a)], where brackets denote zero-one indicators. Then G(i,j)=G(j,i). Nonnegative or normalized weights are unnecessary; no physical record realization is asserted.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_record_book_table.lean:43; Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex, 3721-3749; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 3038-3041

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

omit [Fintype ι] in
theorem APFPaper5.K1.atomTable_symm (w : W → ℝ) (mark : ι → W → Bool) (i j : ι) :
    atomTable w mark i j = atomTable w mark j i := by sorry
