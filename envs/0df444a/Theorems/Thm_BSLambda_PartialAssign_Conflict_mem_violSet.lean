-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_Conflict_mem_violSet
-- name    : BSLambda.PartialAssign.Conflict.mem_violSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:47:42.898076+00:00
-- url     : https://prove2.me/theorems/456f0a60-66ad-4d88-9f99-3915603d03d1
-- title:
--   Conflict: mem viol Set
-- statement:
--   A coordinate at which `P` and `Q` conflict is a literal of `Q` violated by every
--   point of the subcube of `P`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L224-L228
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L224-L228

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

theorem BSLambda.PartialAssign.Conflict.mem_violSet {P Q : PartialAssign V} {v : V} (h : P.Conflict Q v)
    {x : Input V} (hx : P.Sat x) : v ∈ Q.violSet x := by sorry
