-- Prove2me | Theorems.Thm_BSLambda_LLL_Determined_compl
-- name    : BSLambda.LLL.Determined.compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:12:44.93135+00:00
-- url     : https://prove2.me/theorems/e8ff7de6-8aab-424a-bb49-67eee67b1cc6
-- title:
--   Determined: compl
-- statement:
--   The complement of a determined event is determined by the same coordinates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L146-L150
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L146-L150

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

theorem BSLambda.LLL.Determined.compl {S : Finset A} {E : Finset (Cfg β)} (hE : Determined S E) :
    Determined S Eᶜ := by sorry
