-- Prove2me | Theorems.Thm_BSLambda_hammingDist_flipSet
-- name    : BSLambda.hammingDist_flipSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:44:43.066738+00:00
-- url     : https://prove2.me/theorems/e6f1c1dc-72d3-4d82-9eca-5e8b9f7ac9aa
-- title:
--   BSLambda: hamming Dist flip Set
-- statement:
--   The Hamming distance from `x` to `x^A` is exactly `A.card`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L126-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L126-L129

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [Fintype V] [DecidableEq V]

theorem BSLambda.hammingDist_flipSet (x : Input V) (A : Finset V) :
    hammingDist x (flipSet x A) = A.card := by sorry
