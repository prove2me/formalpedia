-- Prove2me | Theorems.Thm_DeciSigma1_Full_Logic_holdsIn_entailmentSentence_iff
-- name    : DeciSigma1.Full.Logic.holdsIn_entailmentSentence_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:21:37.9644+00:00
-- url     : https://prove2.me/theorems/2012f772-4c23-486b-9a3e-d36e0f2107c3
-- title:
--   Logic: holds In entailment Sentence iff
-- statement:
--   A flat constraint over `{⊥, f, ⊤}` entails `x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k` in the class `C`
--   exactly when its entailment sentence holds in `C`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Encodings.lean#L159-L165
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Encodings.lean#L159-L165

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

theorem DeciSigma1.Full.Logic.holdsIn_entailmentSentence_iff (C : Tree n → Prop) (Γ : List (LitT n (Fin m)))
    (q : Fin k → Fin m × Fin m) :
    (entailmentSentence Γ q).HoldsIn C c ↔ DisjEntailsIn C c Γ q := by sorry
