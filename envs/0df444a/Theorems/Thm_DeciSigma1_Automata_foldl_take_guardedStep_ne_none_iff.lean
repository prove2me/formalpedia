-- Prove2me | Theorems.Thm_DeciSigma1_Automata_foldl_take_guardedStep_ne_none_iff
-- name    : DeciSigma1.Automata.foldl_take_guardedStep_ne_none_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:27:59.164181+00:00
-- url     : https://prove2.me/theorems/621b5ddf-3f7e-4e7b-bb97-6f2ea241f2ff
-- title:
--   Automata: foldl take guarded Step ne none iff
-- statement:
--   The Automata construction uses the foldl take guarded Step ne none iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L107-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L107-L118

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

theorem DeciSigma1.Automata.foldl_take_guardedStep_ne_none_iff (s : S) (t : T) {w : List α} {a : ℕ}
    (ha : a ≤ w.length) :
    (w.take a).foldl (guardedStep f g good) (guardedPair good s t) ≠ none ↔
      ∀ j ≤ a, good ((w.take j).foldl f s) ((w.take j).foldl g t) := by sorry
