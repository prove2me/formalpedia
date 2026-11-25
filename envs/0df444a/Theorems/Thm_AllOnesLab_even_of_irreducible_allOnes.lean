-- Prove2me | Theorems.Thm_AllOnesLab_even_of_irreducible_allOnes
-- name    : AllOnesLab.even_of_irreducible_allOnes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:53:53.324802+00:00
-- url     : https://prove2.me/theorems/b602420f-c363-4dde-8edf-39363ee47d0e
-- title:
--   All Ones Lab: even of irreducible all Ones
-- statement:
--   Odd n ≥ 2 forces reducibility: X + 1 divides since eval 1 = n + 1 = 0.
--
--   Source: https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Basic.lean#L89-L104
-- source:
--   https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Basic.lean#L89-L104

import Definitions.Def_AllOnesLab_Defs
import Definitions.Def_AllOnesLab_Basic
set_option autoImplicit true
open Polynomial
open AllOnesLab

theorem AllOnesLab.even_of_irreducible_allOnes (n : ℕ) (hn : 2 ≤ n) (h : Irreducible (allOnes n)) :
    Even n := by sorry
