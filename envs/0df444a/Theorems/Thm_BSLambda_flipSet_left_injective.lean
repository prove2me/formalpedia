-- Prove2me | Theorems.Thm_BSLambda_flipSet_left_injective
-- name    : BSLambda.flipSet_left_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:16.501495+00:00
-- url     : https://prove2.me/theorems/deee11d2-6cd4-40f9-bfb0-9e662680b406
-- title:
--   BSLambda: flip Set left injective
-- statement:
--   Flipping a fixed set of coordinates is injective in the input.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L97-L99
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L97-L99

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]

theorem BSLambda.flipSet_left_injective (A : Finset V) : Function.Injective (flipSet · A) := by sorry
