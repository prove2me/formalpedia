-- Prove2me | Theorems.Thm_BSLambda_ne_flipSet_apply
-- name    : BSLambda.ne_flipSet_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:48:55.730876+00:00
-- url     : https://prove2.me/theorems/b5337a09-0739-49f9-b868-e5ae31226d9c
-- title:
--   BSLambda: ne flip Set apply
-- statement:
--   An input differs from its flip at every flipped coordinate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L68-L69
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L68-L69

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]

theorem BSLambda.ne_flipSet_apply {x : Input V} {A : Finset V} {v : V} (hv : v ∈ A) :
    x v ≠ flipSet x A v := by sorry
