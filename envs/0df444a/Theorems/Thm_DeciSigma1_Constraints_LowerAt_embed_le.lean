-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_LowerAt_embed_le
-- name    : DeciSigma1.Constraints.LowerAt.embed_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:27:34.915529+00:00
-- url     : https://prove2.me/theorems/6de2c1bf-7c70-410a-b8e3-6a6bba759f63
-- title:
--   Lower At: embed le
-- statement:
--   The Lower At construction uses the embed le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L513-L525
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L513-L525

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

theorem DeciSigma1.Constraints.LowerAt.embed_le {π : List (Fin n)} {x y : V}
    (h : LowerAt Γ π x y) {ρ : V → Semantics.Tree n} (hρ : Covariant.Sat ρ Γ) :
    PathBounds.embed Tree.bot π (ρ x) ≤ ρ y := by sorry
