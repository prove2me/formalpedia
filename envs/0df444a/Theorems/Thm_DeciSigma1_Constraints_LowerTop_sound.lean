-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_LowerTop_sound
-- name    : DeciSigma1.Constraints.LowerTop.sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:20:43.171369+00:00
-- url     : https://prove2.me/theorems/386aa2eb-7fd1-410c-87ae-2ec6f6fde2c8
-- title:
--   Lower Top: sound
-- statement:
--   The Lower Top construction uses the sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L95-L101
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L95-L101

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

theorem DeciSigma1.Constraints.LowerTop.sound {Γ : List (LitT n V)} {x : V} {ρ : V → Semantics.Tree n}
    (h : LowerTop Γ x) (hρ : Covariant.Sat ρ Γ) : ρ x = Tree.top := by sorry
