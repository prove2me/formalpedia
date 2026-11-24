-- Prove2me | Theorems.Thm_BSLambda_flipSet_flipSet_symmDiff
-- name    : BSLambda.flipSet_flipSet_symmDiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:48:58.088008+00:00
-- url     : https://prove2.me/theorems/6e451652-86c2-409c-9966-8b6870fd10e7
-- title:
--   BSLambda: flip Set flip Set symm Diff
-- statement:
--   Flipping `A` and then `B` flips exactly the coordinates of the symmetric difference.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L76-L79
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L76-L79

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]

theorem BSLambda.flipSet_flipSet_symmDiff (x : Input V) (A B : Finset V) :
    flipSet (flipSet x A) B = flipSet x (symmDiff A B) := by sorry
