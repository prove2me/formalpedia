-- Prove2me | Theorems.Thm_Falmagne_blockMarschak_not_mem
-- name    : Falmagne.blockMarschak_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:24:34.907912+00:00
-- url     : https://prove2.me/theorems/d7a1a320-8171-4e2a-b68a-d76f9f9edc55
-- title:
--   Falmagne: block Marschak not mem
-- statement:
--   The Falmagne construction uses the block Marschak not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Conservation.lean#L18-L59
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Conservation.lean#L18-L59

module
public import Definitions.Def_EconomicsNextProof_Basic
public import Definitions.Def_EconomicsNextProof_Mobius
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Conservation
set_option autoImplicit true
@[expose] public section
public section
open Falmagne
open Finset
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem Falmagne.blockMarschak_not_mem (p : Finset X → X → ℝ) (hp : IsChoiceRule p)
    (A : Finset X) (x : X) (hx : x ∉ A) :
    blockMarschak p x A = -blockMarschak p x (insert x A) := by sorry
