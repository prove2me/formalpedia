-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_notMem_fixedSet_of_apply_ne
-- name    : BSLambda.PartialAssign.notMem_fixedSet_of_apply_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:49:56.929406+00:00
-- url     : https://prove2.me/theorems/bce06bfe-ab25-4373-8eda-85508423fe7d
-- title:
--   Partial Assign: not Mem fixed Set of apply ne
-- statement:
--   Two points of the same subcube can only differ at a coordinate the subcube leaves free.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L153-L156
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L153-L156

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V]

theorem BSLambda.PartialAssign.notMem_fixedSet_of_apply_ne {P : PartialAssign V} {x y : Input V} (hx : P.Sat x)
    (hy : P.Sat y) {v : V} (hne : x v ≠ y v) : v ∉ P.fixedSet := by sorry
