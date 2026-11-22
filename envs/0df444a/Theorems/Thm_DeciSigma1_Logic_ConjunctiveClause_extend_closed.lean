-- Prove2me | Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_extend_closed
-- name    : DeciSigma1.Logic.ConjunctiveClause.extend_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:10:53.860428+00:00
-- url     : https://prove2.me/theorems/c6b44c3d-220e-4b49-9a17-81ee95e57e6f
-- title:
--   Conjunctive Clause: extend closed
-- statement:
--   The Conjunctive Clause construction uses the extend closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Flatten.lean#L199-L202
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Flatten.lean#L199-L202

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

theorem DeciSigma1.Logic.ConjunctiveClause.extend_closed {C : D → Prop} (hC : I.TermClosed C) {ρ : Fin m → D} (hρ : ∀ v, C (ρ v)) :
    ∀ w, C (c.extend F ρ w)
  := by sorry
