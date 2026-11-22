-- Prove2me | Theorems.Thm_DeciSigma1_Logic_QuantifierFreeFormula_holds_conj
-- name    : DeciSigma1.Logic.QuantifierFreeFormula.holds_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:21:03.181266+00:00
-- url     : https://prove2.me/theorems/e714cc2e-48c2-4d1e-9e66-4be06f25ce20
-- title:
--   Quantifier Free Formula: holds conj
-- statement:
--   The Quantifier Free Formula construction uses the holds conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Encodings.lean#L68-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Encodings.lean#L68-L72

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

theorem DeciSigma1.Logic.QuantifierFreeFormula.holds_conj (ρ : V → D) (φs : List (QuantifierFreeFormula T V)) :
    (conj φs).Holds I ρ ↔ ∀ φ ∈ φs, φ.Holds I ρ := by sorry
