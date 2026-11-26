-- Prove2me | Theorems.Thm_Falmagne_Examples_regularCounterexample_isChoiceRule
-- name    : Falmagne.Examples.regularCounterexample_isChoiceRule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:28:36.662259+00:00
-- url     : https://prove2.me/theorems/81a195a8-c8d2-5262-9cc7-c1fcf2e685a3
-- title:
--   Examples: regular Counterexample is Choice Rule
-- statement:
--   The Examples construction uses the regular Counterexample is Choice Rule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L38-L49
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L38-L49

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

theorem Falmagne.Examples.regularCounterexample_isChoiceRule : IsChoiceRule regularCounterexample := by sorry
