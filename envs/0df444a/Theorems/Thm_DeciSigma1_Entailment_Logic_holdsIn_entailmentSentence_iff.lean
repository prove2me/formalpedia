-- Prove2me | Theorems.Thm_DeciSigma1_Entailment_Logic_holdsIn_entailmentSentence_iff
-- name    : DeciSigma1.Entailment.Logic.holdsIn_entailmentSentence_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:23:15.651733+00:00
-- url     : https://prove2.me/theorems/99b1cf45-8c4b-44a8-957e-25e027200b85
-- title:
--   Logic: holds In entailment Sentence iff
-- statement:
--   A flat constraint over `{⊥, f}` entails `x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k` in the class `C` exactly
--   when its entailment sentence holds in `C`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Encodings.lean#L212-L218
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Encodings.lean#L212-L218

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

theorem DeciSigma1.Entailment.Logic.holdsIn_entailmentSentence_iff (C : PrefixSet n → Prop) (Γ : List (Lit n (Fin m)))
    (q : Fin k → Fin m × Fin m) :
    (entailmentSentence Γ q).HoldsIn C ↔ DisjEntailsIn C Γ q := by sorry
