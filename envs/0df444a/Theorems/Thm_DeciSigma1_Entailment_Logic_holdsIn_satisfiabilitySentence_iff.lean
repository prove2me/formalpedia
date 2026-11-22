-- Prove2me | Theorems.Thm_DeciSigma1_Entailment_Logic_holdsIn_satisfiabilitySentence_iff
-- name    : DeciSigma1.Entailment.Logic.holdsIn_satisfiabilitySentence_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:23:00.177096+00:00
-- url     : https://prove2.me/theorems/a9f6cd5b-5064-4efd-beb1-bfe2d9843032
-- title:
--   Logic: holds In satisfiability Sentence iff
-- statement:
--   A flat constraint over `{⊥, f}` has a solution in the class `C` exactly when its
--   satisfiability sentence holds in `C`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Encodings.lean#L204-L208
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Encodings.lean#L204-L208

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

theorem DeciSigma1.Entailment.Logic.holdsIn_satisfiabilitySentence_iff (C : PrefixSet n → Prop) (Γ : List (Lit n (Fin m))) :
    (satisfiabilitySentence Γ).HoldsIn C ↔ ∃ ρ : Fin m → PrefixSet n, (∀ v, C (ρ v)) ∧ Sat ρ Γ := by sorry
