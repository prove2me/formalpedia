-- Prove2me | Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_extend_name
-- name    : DeciSigma1.Logic.ConjunctiveClause.extend_name
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:36.686008+00:00
-- url     : https://prove2.me/theorems/d6a0373f-0076-4d43-82a8-f635b4bb7808
-- title:
--   Conjunctive Clause: extend name
-- statement:
--   The Conjunctive Clause construction uses the extend name property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Flatten.lean#L221-L223
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Flatten.lean#L221-L223

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

theorem DeciSigma1.Logic.ConjunctiveClause.extend_name (ρ : Fin m → D) {t : T (Fin m)} (ht : t ∈ c.terms F) :
    c.extend F ρ (c.name F t) = I.eval ρ t := by sorry
