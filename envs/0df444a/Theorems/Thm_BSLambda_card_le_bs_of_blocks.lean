-- Prove2me | Theorems.Thm_BSLambda_card_le_bs_of_blocks
-- name    : BSLambda.card_le_bs_of_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:50:15.821557+00:00
-- url     : https://prove2.me/theorems/e028a75b-5cc7-478c-a2b4-88bbab89ae6b
-- title:
--   BSLambda: card le bs of blocks
-- statement:
--   An indexed family of pairwise disjoint sensitive blocks bounds `bs` from below.  The blocks
--   are automatically pairwise distinct, being nonempty and pairwise disjoint.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L152-L157
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L152-L157

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BSLambda.card_le_bs_of_blocks {ι : Type*} {f : Input V → Bool} {x : Input V} {B : ι → Finset V}
    {s : Finset ι} (hsens : ∀ i ∈ s, IsSensitiveBlock f x (B i))
    (hdisj : (s : Set ι).PairwiseDisjoint B) : s.card ≤ bs f := by sorry
