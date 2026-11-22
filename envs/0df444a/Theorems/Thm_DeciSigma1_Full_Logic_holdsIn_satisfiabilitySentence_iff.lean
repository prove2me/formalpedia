-- Prove2me | Theorems.Thm_DeciSigma1_Full_Logic_holdsIn_satisfiabilitySentence_iff
-- name    : DeciSigma1.Full.Logic.holdsIn_satisfiabilitySentence_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:22:01.140798+00:00
-- url     : https://prove2.me/theorems/5d4fde81-9169-48d8-b4b4-80fec9ea5045
-- title:
--   Logic: holds In satisfiability Sentence iff
-- statement:
--   A flat constraint over `{⊥, f, ⊤}` has a solution in the class `C` exactly when its
--   satisfiability sentence holds in `C`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Encodings.lean#L151-L155
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Encodings.lean#L151-L155

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

theorem DeciSigma1.Full.Logic.holdsIn_satisfiabilitySentence_iff (C : Tree n → Prop) (Γ : List (LitT n (Fin m))) :
    (satisfiabilitySentence Γ).HoldsIn C c ↔ Models.SatisfiableIn C c Γ := by sorry
