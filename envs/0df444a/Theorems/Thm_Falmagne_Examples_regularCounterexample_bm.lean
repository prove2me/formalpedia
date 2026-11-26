-- Prove2me | Theorems.Thm_Falmagne_Examples_regularCounterexample_bm
-- name    : Falmagne.Examples.regularCounterexample_bm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:28:43.19996+00:00
-- url     : https://prove2.me/theorems/85567cc0-a464-57fd-a9f4-66abae4f9e6b
-- title:
--   Examples: regular Counterexample bm
-- statement:
--   The Examples construction uses the regular Counterexample bm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L65-L70
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L65-L70

module
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Definitions.Def_EconomicsNextProof_Examples
set_option autoImplicit true
@[expose] public section
public section
open Falmagne Falmagne.Examples
open Finset EconomicsNextProof

theorem Falmagne.Examples.regularCounterexample_bm :
    blockMarschak regularCounterexample (0 : Fin 4) {0} = -1 / 2 := by sorry
