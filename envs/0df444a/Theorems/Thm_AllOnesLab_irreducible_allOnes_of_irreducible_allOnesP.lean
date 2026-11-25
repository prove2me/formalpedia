-- Prove2me | Theorems.Thm_AllOnesLab_irreducible_allOnes_of_irreducible_allOnesP
-- name    : AllOnesLab.irreducible_allOnes_of_irreducible_allOnesP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:53:52.045521+00:00
-- url     : https://prove2.me/theorems/9694cf8c-27b7-4598-9911-ebe6341841f0
-- title:
--   All Ones Lab: irreducible all Ones of irreducible all Ones P
-- statement:
--   The easy direction of P12771: a factorization of allOnes n composes to one of allOnesP n.
--
--   Source: https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Basic.lean#L130-L139
-- source:
--   https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Basic.lean#L130-L139

import Definitions.Def_AllOnesLab_Defs
import Definitions.Def_AllOnesLab_Basic
set_option autoImplicit true
open Polynomial
open AllOnesLab

theorem AllOnesLab.irreducible_allOnes_of_irreducible_allOnesP (n : ℕ) (hn : 2 ≤ n)
    (h : Irreducible (allOnesP n)) : Irreducible (allOnes n) := by sorry
