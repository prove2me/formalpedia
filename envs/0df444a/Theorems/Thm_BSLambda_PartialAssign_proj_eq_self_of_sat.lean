-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_proj_eq_self_of_sat
-- name    : BSLambda.PartialAssign.proj_eq_self_of_sat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:54:57.086448+00:00
-- url     : https://prove2.me/theorems/dda8aef2-d629-4a21-95b4-4938272ed1b3
-- title:
--   Partial Assign: proj eq self of sat
-- statement:
--   The Partial Assign construction uses the proj eq self of sat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L68-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L68-L72

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}

theorem BSLambda.PartialAssign.proj_eq_self_of_sat {P : PartialAssign V} {x : Input V} (hx : P.Sat x) : P.proj x = x := by sorry
