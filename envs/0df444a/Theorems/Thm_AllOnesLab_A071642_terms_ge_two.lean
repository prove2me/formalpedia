-- Prove2me | Theorems.Thm_AllOnesLab_A071642_terms_ge_two
-- name    : AllOnesLab.A071642_terms_ge_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:56:45.265626+00:00
-- url     : https://prove2.me/theorems/1733e5b8-d36c-537d-89a4-e56c335d81c4
-- title:
--   All Ones Lab: A071642 terms ge two
-- statement:
--   The set-level form of the OEIS A071642 comment: the terms `≥ 2` coincide.
--
--   Source: https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Main.lean#L18-L22
-- source:
--   https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Main.lean#L18-L22

import Definitions.Def_AllOnesLab_Hard
import Definitions.Def_AllOnesLab_Main
set_option autoImplicit true
open Polynomial
open AllOnesLab

theorem AllOnesLab.A071642_terms_ge_two :
    {n : ℕ | 2 ≤ n ∧ Irreducible (allOnes n)} = {n : ℕ | 2 ≤ n ∧ Irreducible (allOnesP n)} := by sorry
