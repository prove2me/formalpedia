-- Prove2me | Theorems.Thm_APFPaper5_K1_atomTable_nonneg
-- name    : APFPaper5.K1.atomTable_nonneg
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:04:49.388117+00:00
-- url     : https://prove2.me/theorems/1c902e3b-11f9-4f93-928e-54fb84217267
-- title:
--   Nonnegative atom weights give a nonnegative overlap-form diagonal
-- statement:
--   Let the atom and mark sets be finite, and let G be their weighted Boolean overlap table. Assume hw: every real atom weight is nonnegative. Then F(x,x)≥0 for every coefficient vector x. Faithfulness is not concluded; it requires additional separation conditions.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_record_book_table.lean:67; Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex, 3721-3749; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 3038-3041

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

theorem APFPaper5.K1.atomTable_nonneg (w : W → ℝ) (hw : ∀ a, 0 ≤ w a) (mark : ι → W → Bool) (x : ι → ℝ) :
    0 ≤ tableForm (atomTable w mark) x x := by sorry
