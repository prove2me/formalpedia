-- Prove2me | Theorems.Thm_BSLambda_flipSet_zeroInput_apply
-- name    : BSLambda.flipSet_zeroInput_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:44:33.96564+00:00
-- url     : https://prove2.me/theorems/74baa7db-91b2-4851-befd-1f4da8f517a7
-- title:
--   BSLambda: flip Set zero Input apply
-- statement:
--   Flipping a set of coordinates of the all-zero input yields its indicator function.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L116-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L116-L118

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]

theorem BSLambda.flipSet_zeroInput_apply (A : Finset V) (v : V) :
    flipSet (zeroInput V) A v = decide (v ∈ A) := by sorry
