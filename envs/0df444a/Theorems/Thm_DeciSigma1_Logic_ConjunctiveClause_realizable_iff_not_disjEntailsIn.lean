-- Prove2me | Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_realizable_iff_not_disjEntailsIn
-- name    : DeciSigma1.Logic.ConjunctiveClause.realizable_iff_not_disjEntailsIn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:36.542978+00:00
-- url     : https://prove2.me/theorems/29699d01-8a40-4828-a1c6-b7e588f1574b
-- title:
--   Conjunctive Clause: realizable iff not disj Entails In
-- statement:
--   A clause is realizable in a closed class `C` if and only if its flat constraints do not
--   entail the disjunction of its queries over `C`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Flatten.lean#L246-L272
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Flatten.lean#L246-L272

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

theorem DeciSigma1.Logic.ConjunctiveClause.realizable_iff_not_disjEntailsIn {C : D → Prop} (hC : I.TermClosed C) :
    (∃ ρ : Fin m → D, (∀ v, C (ρ v)) ∧ c.Holds I ρ) ↔
      ¬ F.DisjEntailsIn C (c.constraints F) (c.queries F) := by sorry
