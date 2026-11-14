-- Prove2me | Theorems.Thm_APFPaper5_K1_roleExchange_respects_null
-- name    : APFPaper5.K1.roleExchange_respects_null
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:41:46.58021+00:00
-- url     : https://prove2.me/theorems/86819db8-eaea-43d9-9d75-5f0303301a28
-- title:
--   A symmetric table exchanges row and column nullity
-- statement:
--   Let G be a symmetric real table on a finite index set. Assume hG: G(i,j)=G(j,i), and hx: ΣⱼG(i,j)xⱼ=0 for every row i. Then ΣᵢxᵢG(i,j)=0 for every column j. This is the exact nullity compatibility needed when exchanging coefficient roles in this table model. It does not construct an isomorphism of physical boundary classes, require positivity, or assert that a physical score has this supplied symmetric table.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_mark_table.lean:40; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 353-391;3038-3041

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

theorem APFPaper5.K1.roleExchange_respects_null (G : ι → ι → ℝ) (hG : ∀ i j, G i j = G j i) (x : ι → ℝ)
    (hx : ∀ i, ∑ j, G i j * x j = 0) : ∀ j, ∑ i, x i * G i j = 0 := by sorry
