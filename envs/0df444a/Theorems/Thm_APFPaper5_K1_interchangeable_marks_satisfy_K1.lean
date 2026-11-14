-- Prove2me | Theorems.Thm_APFPaper5_K1_interchangeable_marks_satisfy_K1
-- name    : APFPaper5.K1.interchangeable_marks_satisfy_K1
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:58:31.781208+00:00
-- url     : https://prove2.me/theorems/bb0cc60f-4a46-401d-9da6-7840f3f8e5f6
-- title:
--   An interchangeable table realizes bilinearity and a faithful diagonal
-- statement:
--   Let G be a real table on a finite index set, with diagonal one and constant off-diagonal entry c. Assume hG records this pattern, h0 gives c≥0, and h1 gives c<1. Its coefficient form is real-bilinear and has a faithful nonnegative diagonal when the two coefficient-space roles are identified by the identity equivalence. These are the two displayed algebraic K1 predicates. This model does not construct the physical completed score, its quotient classes, or a physical boundary-role exchange.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_mark_table_instance.lean:39; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 3038-3041;353-391

import Definitions.Def_APFPaper5_K1_OrderedScore
import Theorems.Thm_APFPaper5_K1_tableForm_symm
import Theorems.Thm_APFPaper5_K1_roleExchange_respects_null
import Theorems.Thm_APFPaper5_K1_interchangeable_posDef
import Mathlib.Algebra.Module.Pi

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
universe u
variable {ι : Type u} [Fintype ι]

theorem APFPaper5.K1.interchangeable_marks_satisfy_K1 [DecidableEq ι] (G : ι → ι → ℝ) (c : ℝ)
    (hG : Interchangeable G c) (h0 : 0 ≤ c) (h1 : c < 1) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm G) ∧
      FaithfulNonnegDiagonal (tableForm G) (LinearEquiv.refl ℝ (ι → ℝ)) := by sorry
