-- Prove2me | Theorems.Thm_DeciSigma1_Full_Logic_holds_literal
-- name    : DeciSigma1.Full.Logic.holds_literal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:21:49.927912+00:00
-- url     : https://prove2.me/theorems/1435a7b3-c2f7-4bf5-a548-ae68cd7779d8
-- title:
--   Logic: holds literal
-- statement:
--   The Logic construction uses the holds literal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Encodings.lean#L129-L134
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Encodings.lean#L129-L134

module
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Logic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Logic
public import Definitions.Def_LeanPool_DeciSigma1_Encodings
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Logic
open DeciSigma1.Constraints DeciSigma1.Logic DeciSigma1.Semantics
variable {n k m : ℕ} {V : Type} (c : Fin n → Bool)

theorem DeciSigma1.Full.Logic.holds_literal (ρ : V → Tree n) (l : LitT n V) :
    (literal l).Holds (interpretation c) ρ ↔ HoldsT c ρ l := by sorry
