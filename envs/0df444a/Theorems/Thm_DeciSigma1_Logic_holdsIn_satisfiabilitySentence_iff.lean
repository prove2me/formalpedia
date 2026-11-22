-- Prove2me | Theorems.Thm_DeciSigma1_Logic_holdsIn_satisfiabilitySentence_iff
-- name    : DeciSigma1.Logic.holdsIn_satisfiabilitySentence_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:21:49.958543+00:00
-- url     : https://prove2.me/theorems/b90b82f4-3256-45f0-83e1-65a6b729caa2
-- title:
--   Logic: holds In satisfiability Sentence iff
-- statement:
--   The satisfiability sentence holds in `C` exactly when some assignment with values in `C`
--   satisfies all the formulas.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Encodings.lean#L96-L101
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Encodings.lean#L96-L101

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

theorem DeciSigma1.Logic.holdsIn_satisfiabilitySentence_iff (C : D → Prop)
    (φs : List (QuantifierFreeFormula T (Fin m))) :
    (satisfiabilitySentence φs).HoldsIn I C ↔
      ∃ ρ : Fin m → D, (∀ v, C (ρ v)) ∧ ∀ φ ∈ φs, φ.Holds I ρ := by sorry
