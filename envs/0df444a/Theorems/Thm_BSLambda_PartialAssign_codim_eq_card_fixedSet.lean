-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_codim_eq_card_fixedSet
-- name    : BSLambda.PartialAssign.codim_eq_card_fixedSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:48:59.777043+00:00
-- url     : https://prove2.me/theorems/db77f1ad-0f46-46a9-8573-06d15d797fda
-- title:
--   Partial Assign: codim eq card fixed Set
-- statement:
--   The defining equation for `codim`, so that call sites need not unfold the `def`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L150-L150
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L150-L150

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

theorem BSLambda.PartialAssign.codim_eq_card_fixedSet (P : PartialAssign V) : P.codim = P.fixedSet.card := by sorry
