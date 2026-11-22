-- Prove2me | Theorems.Thm_DeciSigma1_Logic_BooleanSentence_all_iff_not_ex_not
-- name    : DeciSigma1.Logic.BooleanSentence.all_iff_not_ex_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:25.849214+00:00
-- url     : https://prove2.me/theorems/f3e40315-bc2d-437c-8271-051ebac3e533
-- title:
--   Boolean Sentence: all iff not ex not
-- statement:
--   `∀ x, φ` holds exactly when `∃ x, ¬ φ` fails.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Syntax.lean#L125-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Logic/Syntax.lean#L125-L129

module
public import Mathlib.Data.Nat.Notation
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Syntax
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Logic
variable {T : Type → Type} {D V : Type}

theorem DeciSigma1.Logic.BooleanSentence.all_iff_not_ex_not (I : Interpretation T D) (C : D → Prop)
    (s : Sigma1 T) :
    (BooleanSentence.all s).HoldsIn I C ↔
        ¬ (Sigma1.mk s.variableCount (.not s.body)).HoldsIn I C := by sorry
