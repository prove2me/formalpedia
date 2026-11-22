-- Prove2me | Theorems.Thm_DeciSigma1_Logic_QuantifierFreeFormula_holds_disj
-- name    : DeciSigma1.Logic.QuantifierFreeFormula.holds_disj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:20:55.783104+00:00
-- url     : https://prove2.me/theorems/4b8629b3-c9a3-4f40-8598-f5c6f611d556
-- title:
--   Quantifier Free Formula: holds disj
-- statement:
--   The Quantifier Free Formula construction uses the holds disj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Encodings.lean#L74-L78
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Encodings.lean#L74-L78

module
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Logic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Logic
public import Definitions.Def_LeanPool_DeciSigma1_Encodings
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Logic
variable {T : Type → Type} {D V : Type} (I : Interpretation T D)
open DeciSigma1.Logic.QuantifierFreeFormula

theorem DeciSigma1.Logic.QuantifierFreeFormula.holds_disj (ρ : V → D) (φs : List (QuantifierFreeFormula T V)) :
    (disj φs).Holds I ρ ↔ ∃ φ ∈ φs, φ.Holds I ρ := by sorry
