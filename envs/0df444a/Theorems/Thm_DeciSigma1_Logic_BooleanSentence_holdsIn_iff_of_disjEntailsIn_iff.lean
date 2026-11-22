-- Prove2me | Theorems.Thm_DeciSigma1_Logic_BooleanSentence_holdsIn_iff_of_disjEntailsIn_iff
-- name    : DeciSigma1.Logic.BooleanSentence.holdsIn_iff_of_disjEntailsIn_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:06:34.375814+00:00
-- url     : https://prove2.me/theorems/dbb4a974-6432-4b5e-9257-ee51fdbf69a5
-- title:
--   Boolean Sentence: holds In iff of disj Entails In iff
-- statement:
--   If every disjunctive entailment between flat constraints has the same truth value over two
--   closed classes, then so does every Boolean sentence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Decide.lean#L97-L113
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Decide.lean#L97-L113

module
public import Mathlib.Data.Fintype.Sum
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Flatten
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Decide
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Logic
variable {T : Type → Type} {D : Type} {I : Interpretation T D} (F : Flattening I)
variable [∀ m, DecidableEq (T (Fin m))] {C : D → Prop}
omit [(m : ℕ) → DecidableEq (T (Fin m))]

theorem DeciSigma1.Logic.BooleanSentence.holdsIn_iff_of_disjEntailsIn_iff {C C' : D → Prop} (hC : I.TermClosed C)
    (hC' : I.TermClosed C')
    (h : ∀ {W : Type} [Fintype W] [DecidableEq W] {k : ℕ} (Γ : List (F.Lit W))
      (q : Fin k → W × W), F.DisjEntailsIn C Γ q ↔ F.DisjEntailsIn C' Γ q)
    (φ : BooleanSentence T) : φ.HoldsIn I C ↔ φ.HoldsIn I C' := by sorry
