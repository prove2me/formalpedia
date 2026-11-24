-- Prove2me | Theorems.Thm_BSLambda_LLL_card_filter_coord_mul_card
-- name    : BSLambda.LLL.card_filter_coord_mul_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:53:37.039812+00:00
-- url     : https://prove2.me/theorems/53780434-d474-4174-b71c-f56659840528
-- title:
--   LLL: card filter coord mul card
-- statement:
--   **Counting core.**  Pinning one coordinate to a prescribed value divides the number of
--   configurations by the size of that coordinate's alphabet.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L242-L249
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L242-L249

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]

theorem BSLambda.LLL.card_filter_coord_mul_card (a : A) (b : β a) :
    (Finset.univ.filter fun ω : Cfg β => ω a = b).card * Fintype.card (β a)
      = Fintype.card (Cfg β) := by sorry
