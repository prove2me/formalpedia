-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_Closure_close_spec
-- name    : DeciSigma1.Constraints.Closure.close_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:25:35.630743+00:00
-- url     : https://prove2.me/theorems/52d0c2ed-42b7-435c-aa19-1d0ed3f4d6ff
-- title:
--   Closure: close spec
-- statement:
--   Saturation contains its input, is closed under all rules, and preserves
--   the invariant that every stored pair is derivable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L292-L299
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L292-L299

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
variable {n : ℕ} {V : Type*}
variable [Fintype V] [DecidableEq V]
open DeciSigma1.Constraints.Closure

theorem DeciSigma1.Constraints.Closure.close_spec (Γ : List (LitT n V)) (s : Finset (V × V)) :
    s ⊆ close Γ s ∧ expand Γ (close Γ s) ⊆ close Γ s ∧
    ((∀ p ∈ s, Derives Γ p.1 p.2) → ∀ p ∈ close Γ s, Derives Γ p.1 p.2) := by sorry
