-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_mem_violSet_iff_exists_ne
-- name    : BSLambda.PartialAssign.mem_violSet_iff_exists_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:47:59.288813+00:00
-- url     : https://prove2.me/theorems/7ad9f477-4e13-4b6a-8164-93c8e236b2ef
-- title:
--   Partial Assign: mem viol Set iff exists ne
-- statement:
--   `v` is violated by `x` exactly when `P` fixes `v` to a value other than `x v`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L177-L179
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L177-L179

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V]

theorem BSLambda.PartialAssign.mem_violSet_iff_exists_ne {P : PartialAssign V} {x : Input V} {v : V} :
    v ∈ P.violSet x ↔ ∃ b, P v = some b ∧ x v ≠ b := by sorry
