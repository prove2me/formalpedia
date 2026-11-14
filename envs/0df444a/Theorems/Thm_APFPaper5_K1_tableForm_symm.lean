-- Prove2me | Theorems.Thm_APFPaper5_K1_tableForm_symm
-- name    : APFPaper5.K1.tableForm_symm
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:55:58.230175+00:00
-- url     : https://prove2.me/theorems/b478ff7d-01e9-4f35-8ad4-afaad2e8a5c7
-- title:
--   A symmetric finite table gives a symmetric coefficient form
-- statement:
--   Let G be a real table on a finite index set, and assume hG: G(i,j)=G(j,i). Its coefficient form F(x,y)=ΣᵢΣⱼ xᵢG(i,j)yⱼ satisfies F(x,y)=F(y,x). The table is supplied; positivity and any physical symmetry law are not asserted.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_mark_table.lean:33; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 353-391;3038-3041

import Definitions.Def_APFPaper5_K1_MarkTable
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
universe u
variable {ι : Type u} [Fintype ι]

theorem APFPaper5.K1.tableForm_symm (G : ι → ι → ℝ) (hG : ∀ i j, G i j = G j i) (x y : ι → ℝ) :
    tableForm G x y = tableForm G y x := by sorry
