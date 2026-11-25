-- Prove2me | Theorems.Thm_AllOnesLab_main
-- name    : AllOnesLab.main
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:57:20.974224+00:00
-- url     : https://prove2.me/theorems/cc183d5c-ee9b-4483-99f1-59ca74e8193c
-- title:
--   All Ones Lab: main
-- statement:
--   **P12771.** For `n ≥ 2`, `1 + X + ⋯ + Xⁿ` is irreducible over `𝔽₂` iff `1 + P + ⋯ + Pⁿ` is.
--
--   Source: https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Main.lean#L12-L15
-- source:
--   https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Main.lean#L12-L15

import Definitions.Def_AllOnesLab_Hard
import Definitions.Def_AllOnesLab_Main
set_option autoImplicit true
open Polynomial
open AllOnesLab

theorem AllOnesLab.main (n : ℕ) (hn : 2 ≤ n) :
    Irreducible (allOnes n) ↔ Irreducible (allOnesP n) := by sorry
