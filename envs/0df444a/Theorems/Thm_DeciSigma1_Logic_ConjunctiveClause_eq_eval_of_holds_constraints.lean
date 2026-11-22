-- Prove2me | Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_eq_eval_of_holds_constraints
-- name    : DeciSigma1.Logic.ConjunctiveClause.eq_eval_of_holds_constraints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:11:00.604464+00:00
-- url     : https://prove2.me/theorems/c6c59231-cfaf-4043-8069-0d961f49139c
-- title:
--   Conjunctive Clause: eq eval of holds constraints
-- statement:
--   The Conjunctive Clause construction uses the eq eval of holds constraints property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Flatten.lean#L237-L242
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Flatten.lean#L237-L242

module
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Syntax
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Flatten
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Logic
variable {T : Type → Type} {D V : Type} {I : Interpretation T D}
open DeciSigma1.Logic.ConjunctiveClause
variable (F : Flattening I) {m : ℕ} (c : ConjunctiveClause T (Fin m))
variable [DecidableEq (T (Fin m))]

theorem DeciSigma1.Logic.ConjunctiveClause.eq_eval_of_holds_constraints {σ : c.Names F → D}
    (hσ : ∀ l ∈ c.constraints F, F.Holds σ l) {t : T (Fin m)} (ht : t ∈ c.terms F) :
    σ (c.name F t) = I.eval (σ ∘ .inl) t := by sorry
