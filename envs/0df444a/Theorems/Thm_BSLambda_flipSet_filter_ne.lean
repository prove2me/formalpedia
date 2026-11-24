-- Prove2me | Theorems.Thm_BSLambda_flipSet_filter_ne
-- name    : BSLambda.flipSet_filter_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:23.649795+00:00
-- url     : https://prove2.me/theorems/206d71bd-6081-4905-a551-80082049d788
-- title:
--   BSLambda: flip Set filter ne
-- statement:
--   Every input is a flip of every other, at the set of coordinates where they differ.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L140-L143
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L140-L143

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [Fintype V] [DecidableEq V]

theorem BSLambda.flipSet_filter_ne (x y : Input V) :
    flipSet x (Finset.univ.filter fun v ↦ x v ≠ y v) = y := by sorry
