-- Prove2me | Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_mem_terms
-- name    : DeciSigma1.Logic.ConjunctiveClause.mem_terms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:30.220053+00:00
-- url     : https://prove2.me/theorems/d5a1d4b6-ddb3-4cdf-919e-f61dd43fbccb
-- title:
--   Conjunctive Clause: mem terms
-- statement:
--   The Conjunctive Clause construction uses the mem terms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Flatten.lean#L178-L181
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Flatten.lean#L178-L181

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

theorem DeciSigma1.Logic.ConjunctiveClause.mem_terms {p : T (Fin m) × T (Fin m)} (hp : p ∈ c.positive ∨ p ∈ c.negative) :
    p.1 ∈ c.terms F ∧ p.2 ∈ c.terms F := by sorry
