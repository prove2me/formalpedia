-- Prove2me | Theorems.Thm_AaronsonAmbainis_sensitivity_of_block
-- name    : AaronsonAmbainis.sensitivity_of_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:44:01.782187+00:00
-- url     : https://prove2.me/theorems/f31f8339-5120-469d-a6bc-953d490d3890
-- title:
--   Aaronson Ambainis: sensitivity of block
-- statement:
--   The sensitivity bound at every point (Corollary 6.10 of the paper), from the block inequality
--   (Lemma 6.4): the blocks `{j}` are pairwise disjoint.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/DisjointBlocks.lean#L42-L45
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/DisjointBlocks.lean#L42-L45

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Row_DisjointBlocks
set_option autoImplicit true
open AaronsonAmbainis
open Finset

theorem AaronsonAmbainis.sensitivity_of_block : BlockInequality → SensitivityBound := by sorry
