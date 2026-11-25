-- Prove2me | Theorems.Thm_AllOnesLab_irreducible_allOnesP_of_irreducible_allOnes
-- name    : AllOnesLab.irreducible_allOnesP_of_irreducible_allOnes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:56:54.683611+00:00
-- url     : https://prove2.me/theorems/c7f23aca-dde8-50dd-b004-30879920d434
-- title:
--   All Ones Lab: irreducible all Ones P of irreducible all Ones
-- statement:
--   Hard direction of P12771 (Artin–Schreier / trace argument).
--
--   Source: https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Hard.lean#L176-L196
-- source:
--   https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Hard.lean#L176-L196

import Definitions.Def_AllOnesLab_Trace
import Definitions.Def_AllOnesLab_Hard
set_option autoImplicit true
open Polynomial
open AllOnesLab

theorem AllOnesLab.irreducible_allOnesP_of_irreducible_allOnes (n : ℕ) (hn : 2 ≤ n)
    (h : Irreducible (allOnes n)) : Irreducible (allOnesP n) := by sorry
