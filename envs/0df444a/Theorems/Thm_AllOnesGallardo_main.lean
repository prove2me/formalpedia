-- Prove2me | Theorems.Thm_AllOnesGallardo_main
-- name    : AllOnesGallardo.main
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:06:47.991491+00:00
-- url     : https://prove2.me/theorems/90728b37-0620-5cbf-b698-ff2d8c48002e
-- title:
--   All Ones Gallardo: main
-- statement:
--   **P12771.** For `n ≥ 2`, `1 + X + ⋯ + Xⁿ` is irreducible over `𝔽₂` iff `1 + P + ⋯ + Pⁿ` is.
--
--   Source: https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/Solution.lean#L34-L36
-- source:
--   https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/Solution.lean#L34-L36

import Definitions.Def_AllOnesLab
import Definitions.Def_AllOnesComparator_Solution
import Theorems.Thm_AllOnesLab_main

set_option autoImplicit true
open Polynomial
open AllOnesGallardo

theorem AllOnesGallardo.main (n : ℕ) (hn : 2 ≤ n) :
    Irreducible (allOnes n) ↔ Irreducible (allOnesP n) := by sorry
