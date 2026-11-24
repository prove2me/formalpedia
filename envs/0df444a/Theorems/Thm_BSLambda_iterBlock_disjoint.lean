-- Prove2me | Theorems.Thm_BSLambda_iterBlock_disjoint
-- name    : BSLambda.iterBlock_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:54:53.718034+00:00
-- url     : https://prove2.me/theorems/79c3d4dc-7ac0-435e-9a73-c466be0648f9
-- title:
--   BSLambda: iter Block disjoint
-- statement:
--   Distinct index tuples give disjoint Cartesian-product blocks (Section 14).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L169-L174
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L169-L174

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Function
universe u
variable {V ι : Type*} [DecidableEq V] {blk : ι → Finset V}

theorem BSLambda.iterBlock_disjoint (hdisj : Pairwise (Disjoint on blk)) :
    ∀ m : ℕ, Pairwise (Disjoint on (iterBlock blk m))
  := by sorry
