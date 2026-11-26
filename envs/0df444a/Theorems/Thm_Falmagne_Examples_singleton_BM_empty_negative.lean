-- Prove2me | Theorems.Thm_Falmagne_Examples_singleton_BM_empty_negative
-- name    : Falmagne.Examples.singleton_BM_empty_negative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:30:26.679559+00:00
-- url     : https://prove2.me/theorems/cffee8e9-c46a-4d7b-ab13-120c3d8aca6d
-- title:
--   Examples: singleton BM empty negative
-- statement:
--   The Examples construction uses the singleton BM empty negative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L179-L187
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L179-L187

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

theorem Falmagne.Examples.singleton_BM_empty_negative :
    blockMarschak (rankingChoice singletonRanking) (0 : Fin 1) ∅ = -1 := by sorry
