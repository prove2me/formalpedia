-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_Sat_flipSet_singleton
-- name    : BSLambda.PartialAssign.Sat.flipSet_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:32.112049+00:00
-- url     : https://prove2.me/theorems/004f040d-88db-466a-86c4-bd1f63b6d42b
-- title:
--   Sat: flip Set singleton
-- statement:
--   Flipping a coordinate that `P` leaves free keeps the point inside `C(P)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L295-L299
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L295-L299

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V] [DecidableEq V]

theorem BSLambda.PartialAssign.Sat.flipSet_singleton {P : PartialAssign V} {x : Input V} (hx : P.Sat x) {v : V}
    (hv : v ∉ P.fixedSet) : P.Sat (flipSet x {v}) := by sorry
