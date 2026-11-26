-- Prove2me | Theorems.Thm_AME125_cutInj_of_inverse
-- name    : AME125.cutInj_of_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:15:03.639942+00:00
-- url     : https://prove2.me/theorems/e7703add-d8cf-41bd-a60b-ae4d99dc8fce
-- title:
--   AME125: cut Inj of inverse
-- statement:
--   A block with a right inverse is injective: the cut condition follows.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Certificate.lean#L140-L163
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Certificate.lean#L140-L163

module
public import Definitions.Def_AME125_Data
public import Definitions.Def_AME125_GraphState
public import Definitions.Def_AME125_Certificate
set_option autoImplicit false
@[expose] public section
public section
open AME125
open scoped Matrix

theorem AME125.cutInj_of_inverse {n : ℕ} (S : Matrix (Fin n) (Fin n) (ZMod 5)) (A : Finset (Fin n))
    (R : Fin n → Fin n → ZMod 5)
    (h : ∀ i ∈ A, ∀ k ∈ A, ∑ j, (if j ∈ A then 0 else S i j * R j k) = if i = k then 1 else 0) :
    CutInj S A := by sorry
