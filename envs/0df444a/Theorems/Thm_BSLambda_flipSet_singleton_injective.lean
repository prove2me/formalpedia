-- Prove2me | Theorems.Thm_BSLambda_flipSet_singleton_injective
-- name    : BSLambda.flipSet_singleton_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:49:44.951549+00:00
-- url     : https://prove2.me/theorems/357f3f01-1099-44bf-ba19-b11dd81e6ed5
-- title:
--   BSLambda: flip Set singleton injective
-- statement:
--   Distinct coordinates give distinct single-coordinate flips of a fixed input.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L106-L109
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L106-L109

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]

theorem BSLambda.flipSet_singleton_injective (x : Input V) :
    Function.Injective fun v : V ↦ flipSet x {v} := by sorry
