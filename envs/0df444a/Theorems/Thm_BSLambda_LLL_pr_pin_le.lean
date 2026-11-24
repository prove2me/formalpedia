-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_pin_le
-- name    : BSLambda.LLL.pr_pin_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:53:44.547513+00:00
-- url     : https://prove2.me/theorems/280cb932-4e3e-4327-9b8e-fdfd9ac42d77
-- title:
--   LLL: pr pin le
-- statement:
--   Pinning several coordinates into target sets of size at most `m`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L294-L300
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L294-L300

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
variable [∀ a, Nonempty (β a)]

theorem BSLambda.LLL.pr_pin_le (T : Finset A) (s : (a : A) → Finset (β a)) (m : ℕ)
    (hm : ∀ a ∈ T, (s a).card ≤ m) :
    pr (Finset.univ.filter fun ω : Cfg β => ∀ a ∈ T, ω a ∈ s a)
      ≤ ∏ a ∈ T, (m : ℝ) / (Fintype.card (β a) : ℝ) := by sorry
