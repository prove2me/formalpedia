-- Prove2me | Theorems.Thm_BSLambda_LLL_determined_pin
-- name    : BSLambda.LLL.determined_pin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:04.417269+00:00
-- url     : https://prove2.me/theorems/bc1484e5-d825-40b5-a963-139a993ad873
-- title:
--   LLL: determined pin
-- statement:
--   A pinning event is determined by the coordinates it pins.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L167-L170
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L167-L170

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

theorem BSLambda.LLL.determined_pin (T : Finset A) (s : (a : A) → Finset (β a)) :
    Determined T (Finset.univ.filter fun ω : Cfg β => ∀ a ∈ T, ω a ∈ s a) := by sorry
