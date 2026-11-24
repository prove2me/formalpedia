-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_Sat_eq_of_fixed
-- name    : BSLambda.PartialAssign.Sat.eq_of_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:47:40.207801+00:00
-- url     : https://prove2.me/theorems/424a2195-f0fe-457b-aa62-666ce9481830
-- title:
--   Sat: eq of fixed
-- statement:
--   The Sat construction uses the eq of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L53-L54
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L53-L54

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}

theorem BSLambda.PartialAssign.Sat.eq_of_fixed {P : PartialAssign V} {x : Input V} (hx : P.Sat x) {v : V} {b : Bool}
    (hv : P v = some b) : x v = b := by sorry
