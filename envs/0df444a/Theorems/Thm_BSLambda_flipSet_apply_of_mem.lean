-- Prove2me | Theorems.Thm_BSLambda_flipSet_apply_of_mem
-- name    : BSLambda.flipSet_apply_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:46:26.85095+00:00
-- url     : https://prove2.me/theorems/4502c4e5-2ec1-4355-bcfa-507dd5a98612
-- title:
--   BSLambda: flip Set apply of mem
-- statement:
--   The BSLambda construction uses the flip Set apply of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L51-L52
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Cube.lean#L51-L52

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [DecidableEq V]

theorem BSLambda.flipSet_apply_of_mem {x : Input V} {A : Finset V} {v : V} (hv : v ∈ A) :
    flipSet x A v = !x v := by sorry
