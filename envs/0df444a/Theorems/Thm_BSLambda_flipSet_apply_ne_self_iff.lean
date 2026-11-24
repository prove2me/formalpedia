-- Prove2me | Theorems.Thm_BSLambda_flipSet_apply_ne_self_iff
-- name    : BSLambda.flipSet_apply_ne_self_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:49:41.997462+00:00
-- url     : https://prove2.me/theorems/8d2b79f7-cb64-4387-817a-a9b805b964e7
-- title:
--   BSLambda: flip Set apply ne self iff
-- statement:
--   A coordinate is changed by `flipSet` exactly when it lies in the flipped set.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L63-L65
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L63-L65

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]

theorem BSLambda.flipSet_apply_ne_self_iff {x : Input V} {A : Finset V} {v : V} :
    flipSet x A v ≠ x v ↔ v ∈ A := by sorry
