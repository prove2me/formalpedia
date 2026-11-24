-- Prove2me | Theorems.Thm_BSLambda_flipSet_apply_of_notMem
-- name    : BSLambda.flipSet_apply_of_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:44:29.375107+00:00
-- url     : https://prove2.me/theorems/295b3e10-1ce0-4248-b55a-10b21ea1d2d2
-- title:
--   BSLambda: flip Set apply of not Mem
-- statement:
--   The BSLambda construction uses the flip Set apply of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L54-L55
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L54-L55

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]

theorem BSLambda.flipSet_apply_of_notMem {x : Input V} {A : Finset V} {v : V} (hv : v ∉ A) :
    flipSet x A v = x v := by sorry
