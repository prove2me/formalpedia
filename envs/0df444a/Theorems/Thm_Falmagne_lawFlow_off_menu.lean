-- Prove2me | Theorems.Thm_Falmagne_lawFlow_off_menu
-- name    : Falmagne.lawFlow_off_menu
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:13:49.575836+00:00
-- url     : https://prove2.me/theorems/638af95b-7ce2-4551-b05c-75cf9d21e345
-- title:
--   Falmagne: law Flow off menu
-- statement:
--   The Falmagne construction uses the law Flow off menu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Representation.lean#L33-L35
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Representation.lean#L33-L35

module
public import Definitions.Def_EconomicsNextProof_Basic
public import Definitions.Def_EconomicsNextProof_Representation
set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x : X}

theorem Falmagne.lawFlow_off_menu (w : RankingLaw X) (hx : x ∉ A) :
    lawFlow w x A = 0 := by sorry
