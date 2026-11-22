-- Prove2me | Theorems.Thm_DeciSigma1_Entailment_Logic_holds_literal
-- name    : DeciSigma1.Entailment.Logic.holds_literal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:20:51.597852+00:00
-- url     : https://prove2.me/theorems/831d750b-e1ac-4467-8c60-00698366751a
-- title:
--   Logic: holds literal
-- statement:
--   The Logic construction uses the holds literal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Encodings.lean#L183-L187
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Encodings.lean#L183-L187

module
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Logic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Logic
public import Definitions.Def_LeanPool_DeciSigma1_Encodings
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Entailment DeciSigma1.Entailment.Logic
open DeciSigma1.Constraints.TopFree DeciSigma1.Logic DeciSigma1.Semantics
variable {n k m : ℕ} {V : Type}

theorem DeciSigma1.Entailment.Logic.holds_literal (ρ : V → PrefixSet n) (l : Lit n V) :
    (literal l).Holds (interpretation n) ρ ↔ l.Holds ρ := by sorry
