-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_UpperAt_map
-- name    : DeciSigma1.Constraints.UpperAt.map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:20:17.238798+00:00
-- url     : https://prove2.me/theorems/d0507364-72c6-4a1d-a431-ef153af0d01d
-- title:
--   Upper At: map
-- statement:
--   The Upper At construction uses the map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L484-L490
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L484-L490

module
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}

theorem DeciSigma1.Constraints.UpperAt.map {W : Type*} {ψ : List (LitT n W)} (r : V → W)
    (hr : ∀ l ∈ Γ, l.map r ∈ ψ) {π : List (Fin n)} {a b : V}
    (h : UpperAt Γ π a b) : UpperAt ψ π (r a) (r b) := by sorry
