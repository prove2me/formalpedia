-- Prove2me | Theorems.Thm_BSLambda_flipSet_singleton_flipSet_singleton
-- name    : BSLambda.flipSet_singleton_flipSet_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:48:58.392973+00:00
-- url     : https://prove2.me/theorems/2da311dd-3e1b-4110-8ddd-f53cde9a57dd
-- title:
--   BSLambda: flip Set singleton flip Set singleton
-- statement:
--   Flipping two distinct coordinates one after the other is the same as flipping the pair
--   at once.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L86-L88
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L86-L88

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]

theorem BSLambda.flipSet_singleton_flipSet_singleton (x : Input V) {p q : V} (hpq : p ≠ q) :
    flipSet (flipSet x {p}) {q} = flipSet x {p, q} := by sorry
