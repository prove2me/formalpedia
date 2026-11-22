-- Prove2me | Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_mem_terms_of_mem_subterms
-- name    : DeciSigma1.Logic.ConjunctiveClause.mem_terms_of_mem_subterms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:28.833948+00:00
-- url     : https://prove2.me/theorems/d2fdab4c-d24d-4c73-89a6-ac55f431a97d
-- title:
--   Conjunctive Clause: mem terms of mem subterms
-- statement:
--   The Conjunctive Clause construction uses the mem terms of mem subterms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Flatten.lean#L183-L189
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Flatten.lean#L183-L189

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

theorem DeciSigma1.Logic.ConjunctiveClause.mem_terms_of_mem_subterms {s t : T (Fin m)} (ht : t ∈ c.terms F)
    (hs : s ∈ F.subterms t) : s ∈ c.terms F := by sorry
