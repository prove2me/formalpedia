-- Prove2me | Theorems.Thm_BSLambda_hammingDist_flipSet_flipSet
-- name    : BSLambda.hammingDist_flipSet_flipSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:21.455521+00:00
-- url     : https://prove2.me/theorems/2d5e2347-9c9a-4157-8f4a-f2c51156c719
-- title:
--   BSLambda: hamming Dist flip Set flip Set
-- statement:
--   Two flips of the same input differ exactly on the symmetric difference of the flipped
--   sets.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L133-L137
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L133-L137

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [Fintype V] [DecidableEq V]

theorem BSLambda.hammingDist_flipSet_flipSet (x : Input V) (A B : Finset V) :
    hammingDist (flipSet x A) (flipSet x B) = (symmDiff A B).card := by sorry
