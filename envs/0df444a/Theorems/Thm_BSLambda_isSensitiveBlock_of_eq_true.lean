-- Prove2me | Theorems.Thm_BSLambda_isSensitiveBlock_of_eq_true
-- name    : BSLambda.isSensitiveBlock_of_eq_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:50:13.885134+00:00
-- url     : https://prove2.me/theorems/03b1dd61-a484-4766-ac41-7908371bc020
-- title:
--   BSLambda: is Sensitive Block of eq true
-- statement:
--   The usual way to exhibit a sensitive block: a nonempty `A` that turns `f` from `false`
--   to `true`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L94-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L94-L97

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]

theorem BSLambda.isSensitiveBlock_of_eq_true {f : Input V → Bool} {x : Input V} {A : Finset V}
    (hA : A.Nonempty) (hx : f x = false) (hflip : f (flipSet x A) = true) :
    IsSensitiveBlock f x A := by sorry
