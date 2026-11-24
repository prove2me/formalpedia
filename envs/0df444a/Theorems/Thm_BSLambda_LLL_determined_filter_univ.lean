-- Prove2me | Theorems.Thm_BSLambda_LLL_determined_filter_univ
-- name    : BSLambda.LLL.determined_filter_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:49:28.294425+00:00
-- url     : https://prove2.me/theorems/7e2a9739-db89-467c-bb77-91243fb7d79a
-- title:
--   LLL: determined filter univ
-- statement:
--   The standard way to exhibit a determined event: an event cut out of the whole space by a
--   predicate that only reads the coordinates in `S`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L155-L157
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L155-L157

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
omit [(a : A) → DecidableEq (β a)]

theorem BSLambda.LLL.determined_filter_univ {S : Finset A} (p : Cfg β → Prop) [DecidablePred p]
    (hp : ∀ ω ω' : Cfg β, (∀ a ∈ S, ω a = ω' a) → (p ω ↔ p ω')) :
    Determined S (Finset.univ.filter p) := by sorry
