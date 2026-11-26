-- Prove2me | Theorems.Thm_Falmagne_Examples_regularCounterexample_bm_negative
-- name    : Falmagne.Examples.regularCounterexample_bm_negative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:28:53.707833+00:00
-- url     : https://prove2.me/theorems/657f3818-bd6d-4c44-9495-5439c49afd4f
-- title:
--   Examples: regular Counterexample bm negative
-- statement:
--   The Examples construction uses the regular Counterexample bm negative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L72-L75
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L72-L75

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

theorem Falmagne.Examples.regularCounterexample_bm_negative :
    blockMarschak regularCounterexample (0 : Fin 4) {0} < 0 := by sorry
