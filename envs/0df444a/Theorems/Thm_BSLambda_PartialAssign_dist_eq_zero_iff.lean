-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_dist_eq_zero_iff
-- name    : BSLambda.PartialAssign.dist_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:45:11.422808+00:00
-- url     : https://prove2.me/theorems/f811445a-c7e5-48af-b6f3-ec0abb59edb4
-- title:
--   Partial Assign: dist eq zero iff
-- statement:
--   The Partial Assign construction uses the dist eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L203-L206
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L203-L206

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

theorem BSLambda.PartialAssign.dist_eq_zero_iff {P : PartialAssign V} {x : Input V} : P.dist x = 0 ↔ P.Sat x := by sorry
