-- Prove2me | Theorems.Thm_Falmagne_Examples_mixture_BM_nonnegative
-- name    : Falmagne.Examples.mixture_BM_nonnegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:29:01.613774+00:00
-- url     : https://prove2.me/theorems/a5914a4f-2175-5e6f-be56-bd5538a9f469
-- title:
--   Examples: mixture BM nonnegative
-- statement:
--   The Examples construction uses the mixture BM nonnegative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L175-L177
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L175-L177

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

theorem Falmagne.Examples.mixture_BM_nonnegative :
    ∀ x A, x ∈ A → 0 ≤ blockMarschak mixtureChoice x A := by sorry
