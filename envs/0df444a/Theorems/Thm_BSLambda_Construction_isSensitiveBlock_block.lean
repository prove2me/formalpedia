-- Prove2me | Theorems.Thm_BSLambda_Construction_isSensitiveBlock_block
-- name    : BSLambda.Construction.isSensitiveBlock_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:53:10.279282+00:00
-- url     : https://prove2.me/theorems/ff5c8d42-cc3f-4f98-b196-6d2dfdc7d618
-- title:
--   Construction: is Sensitive Block block
-- statement:
--   Each block `B_i` is a sensitive block of `f` at the all-zero input (Section 5).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/BlockSens.lean#L57-L59
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/BlockSens.lean#L57-L59

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r}

theorem BSLambda.Construction.isSensitiveBlock_block [Fintype ι] [DecidableEq ι] [NeZero r] (i : ι) :
    IsSensitiveBlock (ind Arc γ) (zeroInput (Coord ι r)) (block i) := by sorry
