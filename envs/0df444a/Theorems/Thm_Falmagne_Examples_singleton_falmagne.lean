-- Prove2me | Theorems.Thm_Falmagne_Examples_singleton_falmagne
-- name    : Falmagne.Examples.singleton_falmagne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:30:26.594476+00:00
-- url     : https://prove2.me/theorems/59bd9323-b595-4907-8bc0-b8e95731ccd6
-- title:
--   Examples: singleton falmagne
-- statement:
--   A positive singleton case also instantiates the completed characterization.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L190-L193
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L190-L193

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

theorem Falmagne.Examples.singleton_falmagne :
    RandomUtilityRepresentable (rankingChoice singletonRanking) ↔
      BlockMarschakNonnegative (rankingChoice singletonRanking) := by sorry
