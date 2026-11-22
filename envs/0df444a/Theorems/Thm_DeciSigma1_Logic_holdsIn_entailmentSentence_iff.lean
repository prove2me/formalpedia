-- Prove2me | Theorems.Thm_DeciSigma1_Logic_holdsIn_entailmentSentence_iff
-- name    : DeciSigma1.Logic.holdsIn_entailmentSentence_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:20:44.187229+00:00
-- url     : https://prove2.me/theorems/2d634b65-ceba-487a-82f1-0642f4e4998c
-- title:
--   Logic: holds In entailment Sentence iff
-- statement:
--   The entailment sentence holds in `C` exactly when every assignment with values in `C` that
--   satisfies the formulas `φs` satisfies one of the formulas `ψs`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Encodings.lean#L105-L110
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Encodings.lean#L105-L110

module
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Logic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Logic
public import Definitions.Def_LeanPool_DeciSigma1_Encodings
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Logic
variable {T : Type → Type} {D V : Type} (I : Interpretation T D)
variable {m : ℕ}

theorem DeciSigma1.Logic.holdsIn_entailmentSentence_iff (C : D → Prop)
    (φs ψs : List (QuantifierFreeFormula T (Fin m))) :
    (entailmentSentence φs ψs).HoldsIn I C ↔
      ∀ ρ : Fin m → D, (∀ v, C (ρ v)) → (∀ φ ∈ φs, φ.Holds I ρ) → ∃ ψ ∈ ψs, ψ.Holds I ρ := by sorry
