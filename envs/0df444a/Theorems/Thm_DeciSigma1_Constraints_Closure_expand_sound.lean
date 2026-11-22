-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_Closure_expand_sound
-- name    : DeciSigma1.Constraints.Closure.expand_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:25:25.611313+00:00
-- url     : https://prove2.me/theorems/90a45ab3-5c3d-4b2e-bf66-4f1124676ca3
-- title:
--   Closure: expand sound
-- statement:
--   The Closure construction uses the expand sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L264-L274
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L264-L274

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

theorem DeciSigma1.Constraints.Closure.expand_sound (Γ : List (LitT n V)) (s : Finset (V × V))
    (hs : ∀ p ∈ s, Derives Γ p.1 p.2) :
    ∀ p ∈ expand Γ s, Derives Γ p.1 p.2 := by sorry
