-- Prove2me | Theorems.Thm_Falmagne_upperSum_lawFlow
-- name    : Falmagne.upperSum_lawFlow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:13:59.763178+00:00
-- url     : https://prove2.me/theorems/7fb5f760-03f4-40ac-8d92-3fe2412bf275
-- title:
--   Falmagne: upper Sum law Flow
-- statement:
--   The Falmagne construction uses the upper Sum law Flow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/ChoiceMobius.lean#L34-L43
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/ChoiceMobius.lean#L34-L43

module
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Mobius
public import Definitions.Def_EconomicsNextProof_ChoiceMobius
set_option autoImplicit true
@[expose] public section
public section
open Falmagne
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x : X}

theorem Falmagne.upperSum_lawFlow (w : RankingLaw X) (hw : ∀ l ∈ w.support, IsRanking l)
    (x : X) (A : Finset X) (hx : x ∈ A) :
    upperSum (lawFlow w x) A = w.sum (fun l a => a * rankingChoice l A x) := by sorry
