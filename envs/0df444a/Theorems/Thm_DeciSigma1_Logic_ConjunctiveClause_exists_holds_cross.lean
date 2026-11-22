-- Prove2me | Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_exists_holds_cross
-- name    : DeciSigma1.Logic.ConjunctiveClause.exists_holds_cross
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:10:43.332792+00:00
-- url     : https://prove2.me/theorems/cb9464b1-d7b8-434c-9af0-86df0a1c6103
-- title:
--   Conjunctive Clause: exists holds cross
-- statement:
--   The Conjunctive Clause construction uses the exists holds cross property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Flatten.lean#L80-L83
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Flatten.lean#L80-L83

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

theorem DeciSigma1.Logic.ConjunctiveClause.exists_holds_cross (ρ : V → D) (cs ds : List (ConjunctiveClause T V)) :
    (∃ c ∈ cross cs ds, c.Holds I ρ) ↔ (∃ c ∈ cs, c.Holds I ρ) ∧ (∃ d ∈ ds, d.Holds I ρ) := by sorry
