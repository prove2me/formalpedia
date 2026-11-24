-- Prove2me | Theorems.Thm_BSLambda_LLL_Determined_inter
-- name    : BSLambda.LLL.Determined.inter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:12:41.669196+00:00
-- url     : https://prove2.me/theorems/fc8df14e-89e1-4411-8692-1f511375c95a
-- title:
--   Determined: inter
-- statement:
--   The intersection of two determined events is determined by the union of the supports.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L138-L143
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L138-L143

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
omit [(a : A) → Fintype (β a)]

theorem BSLambda.LLL.Determined.inter {S T : Finset A} {E F : Finset (Cfg β)} (hE : Determined S E)
    (hF : Determined T F) : Determined (S ∪ T) (E ∩ F) := by sorry
