-- Prove2me | Theorems.Thm_DeciSigma1_Automata_foldl_guardedStep_eq_some
-- name    : DeciSigma1.Automata.foldl_guardedStep_eq_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:28:10.312048+00:00
-- url     : https://prove2.me/theorems/36642593-8afe-4dec-bfc1-a85682d003c6
-- title:
--   Automata: foldl guarded Step eq some
-- statement:
--   The Automata construction uses the foldl guarded Step eq some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L120-L126
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L120-L126

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
open DeciSigma1.Constraints
open DeciSigma1.Automata
variable {α S T : Type}
variable (f : S → α → S) (g : T → α → T) (good : S → T → Prop) [∀ s t, Decidable (good s t)]

theorem DeciSigma1.Automata.foldl_guardedStep_eq_some (s : S) (t : T) {w : List α}
    (h : w.foldl (guardedStep f g good) (guardedPair good s t) ≠ none) :
    w.foldl (guardedStep f g good) (guardedPair good s t) = some (w.foldl f s, w.foldl g t) := by sorry
