-- Prove2me | Theorems.Thm_DeciSigma1_Full_Logic_booleanSentence_regular_iff
-- name    : DeciSigma1.Full.Logic.booleanSentence_regular_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:18:22.385803+00:00
-- url     : https://prove2.me/theorems/f3c74450-ad32-4bbc-80dc-bef2e1758c3b
-- title:
--   Logic: boolean Sentence regular iff
-- statement:
--   A sentence over `{⊥, f, ⊤}` has the same truth value over regular and over arbitrary
--   trees.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Logic.lean#L287-L292
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Logic.lean#L287-L292

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Full_Logic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Logic
open DeciSigma1.Constraints DeciSigma1.Semantics DeciSigma1.Full.Models
variable {n : ℕ} {V W : Type}
variable (c : Fin n → Bool)

theorem DeciSigma1.Full.Logic.booleanSentence_regular_iff (φ : BooleanSentence n) :
    φ.HoldsIn RegularTop c ↔ φ.HoldsIn (fun _ => True) c := by sorry
