-- Prove2me | Theorems.Thm_BSLambda_flipSet_left_inj
-- name    : BSLambda.flipSet_left_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:44:32.832094+00:00
-- url     : https://prove2.me/theorems/f3ba2b7c-e44c-4230-bbe2-d0f06ee8d71f
-- title:
--   BSLambda: flip Set left inj
-- statement:
--   The BSLambda construction uses the flip Set left inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L101-L103
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L101-L103

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]

theorem BSLambda.flipSet_left_inj {x y : Input V} {A : Finset V} :
    flipSet x A = flipSet y A ↔ x = y := by sorry
