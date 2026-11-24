-- Prove2me | Theorems.Thm_BSLambda_isBlockFamily_image
-- name    : BSLambda.isBlockFamily_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:56.228732+00:00
-- url     : https://prove2.me/theorems/c1a8e4c5-1161-4eb9-8725-9f66ade226eb
-- title:
--   BSLambda: is Block Family image
-- statement:
--   Sensitive blocks indexed by a `Finset ι` and pairwise disjoint on it form a block family.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L138-L148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L138-L148

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]

theorem BSLambda.isBlockFamily_image {ι : Type*} {f : Input V → Bool} {x : Input V} {B : ι → Finset V}
    {s : Finset ι} (hsens : ∀ i ∈ s, IsSensitiveBlock f x (B i))
    (hdisj : (s : Set ι).PairwiseDisjoint B) :
    IsBlockFamily f x (s.image B) := by sorry
