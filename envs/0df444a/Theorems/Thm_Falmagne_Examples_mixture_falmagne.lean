-- Prove2me | Theorems.Thm_Falmagne_Examples_mixture_falmagne
-- name    : Falmagne.Examples.mixture_falmagne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:30:31.165697+00:00
-- url     : https://prove2.me/theorems/1ba02c9e-689f-4043-9226-ff01767e859e
-- title:
--   Examples: mixture falmagne
-- statement:
--   Sparse choice probabilities, including exact zeros, satisfy the completed theorem.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L196-L198
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L196-L198

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

theorem Falmagne.Examples.mixture_falmagne :
    RandomUtilityRepresentable mixtureChoice ↔ BlockMarschakNonnegative mixtureChoice := by sorry
