-- Prove2me | Theorems.Thm_Falmagne_blockMarschak_source
-- name    : Falmagne.blockMarschak_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:24:39.718925+00:00
-- url     : https://prove2.me/theorems/aa5c2a27-679a-55cc-a21a-a52b7898b7ce
-- title:
--   Falmagne: block Marschak source
-- statement:
--   The Falmagne construction uses the block Marschak source property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Conservation.lean#L71-L74
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Conservation.lean#L71-L74

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

theorem Falmagne.blockMarschak_source [Nonempty X] (p : Finset X → X → ℝ)
    (hp : IsChoiceRule p) : ∑ x : X, blockMarschak p x univ = 1 := by sorry
