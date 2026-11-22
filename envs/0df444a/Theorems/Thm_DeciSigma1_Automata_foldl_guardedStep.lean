-- Prove2me | Theorems.Thm_DeciSigma1_Automata_foldl_guardedStep
-- name    : DeciSigma1.Automata.foldl_guardedStep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:23:55.119391+00:00
-- url     : https://prove2.me/theorems/4858cd76-210d-428a-acd7-95633194aca5
-- title:
--   Automata: foldl guarded Step
-- statement:
--   The guarded product follows both runs as long as every prefix leads to a good pair, and
--   is dead afterward.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L87-L105
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L87-L105

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

theorem DeciSigma1.Automata.foldl_guardedStep (s : S) (t : T) (w : List α) :
    w.foldl (guardedStep f g good) (guardedPair good s t) =
      if ∀ j ≤ w.length, good ((w.take j).foldl f s) ((w.take j).foldl g t) then
        some (w.foldl f s, w.foldl g t) else none := by sorry
