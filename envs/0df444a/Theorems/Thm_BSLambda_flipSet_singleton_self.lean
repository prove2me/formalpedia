-- Prove2me | Theorems.Thm_BSLambda_flipSet_singleton_self
-- name    : BSLambda.flipSet_singleton_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:19.772582+00:00
-- url     : https://prove2.me/theorems/188ecdf7-17cb-48aa-93a9-a542c77d6630
-- title:
--   BSLambda: flip Set singleton self
-- statement:
--   The flipped coordinate of a single-coordinate flip.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L112-L113
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L112-L113

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]

theorem BSLambda.flipSet_singleton_self (x : Input V) (v : V) : flipSet x {v} v = !x v := by sorry
