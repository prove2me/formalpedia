-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_exists_eq_comp_of_mem_typeClass
-- name    : ArithmeticTriangleRemovalInVectorSpaces.exists_eq_comp_of_mem_typeClass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:35.27907+00:00
-- url     : https://prove2.me/theorems/98217ba1-030e-4aca-9346-5c2ca790bd45
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: exists eq comp of mem type Class
-- statement:
--   The Arithmetic Triangle Removal In Vector Spaces construction uses the exists eq comp of mem type Class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/TypeClass.lean#L63-L69
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/TypeClass.lean#L63-L69

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Perm
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_LogSumSupport
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_TypeClass
set_option autoImplicit true
@[expose] public section
public section
open Finset Real
open ArithmeticTriangleRemovalInVectorSpaces
variable {n N : ℕ} {a b b' : Fin n → ℕ}

theorem ArithmeticTriangleRemovalInVectorSpaces.exists_eq_comp_of_mem_typeClass (hb : b ∈ typeClass a) (hb' : b' ∈ typeClass a) :
    ∃ σ : Equiv.Perm (Fin n), b' = b ∘ σ := by sorry
