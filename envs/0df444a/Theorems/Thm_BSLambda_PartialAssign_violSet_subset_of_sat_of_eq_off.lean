-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_violSet_subset_of_sat_of_eq_off
-- name    : BSLambda.PartialAssign.violSet_subset_of_sat_of_eq_off
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:49:05.456873+00:00
-- url     : https://prove2.me/theorems/4c422066-cefb-4a1e-85c5-344d01ed325b
-- title:
--   Partial Assign: viol Set subset of sat of eq off
-- statement:
--   A point that agrees outside `A` with some point of `C(P)` violates no literal of `P`
--   outside `A`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L186-L191
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L186-L191

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

theorem BSLambda.PartialAssign.violSet_subset_of_sat_of_eq_off {P : PartialAssign V} {x y : Input V} {A : Finset V}
    (hx : P.Sat x) (h : ∀ v ∉ A, y v = x v) : P.violSet y ⊆ A := by sorry
