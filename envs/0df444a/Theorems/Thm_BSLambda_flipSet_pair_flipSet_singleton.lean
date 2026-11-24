-- Prove2me | Theorems.Thm_BSLambda_flipSet_pair_flipSet_singleton
-- name    : BSLambda.flipSet_pair_flipSet_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:49:41.300921+00:00
-- url     : https://prove2.me/theorems/ca542ae1-a009-432d-aa6b-429490e87e10
-- title:
--   BSLambda: flip Set pair flip Set singleton
-- statement:
--   Undoing one half of a pair flip leaves the single flip at the other coordinate: this is
--   the "other midpoint" identity behind every two-midpoint argument.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L92-L94
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L92-L94

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]

theorem BSLambda.flipSet_pair_flipSet_singleton (x : Input V) {p q : V} (hpq : p ≠ q) :
    flipSet (flipSet x {p, q}) {q} = flipSet x {p} := by sorry
