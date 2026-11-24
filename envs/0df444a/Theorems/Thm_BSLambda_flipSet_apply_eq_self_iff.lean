-- Prove2me | Theorems.Thm_BSLambda_flipSet_apply_eq_self_iff
-- name    : BSLambda.flipSet_apply_eq_self_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:44:29.508362+00:00
-- url     : https://prove2.me/theorems/1fc5f36d-e056-49f6-8233-3bfbb1d7708a
-- title:
--   BSLambda: flip Set apply eq self iff
-- statement:
--   A coordinate survives `flipSet` exactly when it lies outside the flipped set.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L58-L60
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L58-L60

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]

theorem BSLambda.flipSet_apply_eq_self_iff {x : Input V} {A : Finset V} {v : V} :
    flipSet x A v = x v ↔ v ∉ A := by sorry
