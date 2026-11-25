-- Prove2me | Theorems.Thm_AllOnesLab_allOnes_coeff_eq
-- name    : AllOnesLab.allOnes_coeff_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:52:28.002795+00:00
-- url     : https://prove2.me/theorems/10974841-e339-5938-8164-d4b81a93bfbe
-- title:
--   All Ones Lab: all Ones coeff eq
-- statement:
--   All coefficients up to `n` are `1`, the rest vanish.
--
--   Source: https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Basic.lean#L40-L42
-- source:
--   https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Basic.lean#L40-L42

import Definitions.Def_AllOnesLab_Defs
import Definitions.Def_AllOnesLab_Basic
set_option autoImplicit true
open Polynomial
open AllOnesLab

theorem AllOnesLab.allOnes_coeff_eq (n i : ℕ) : (allOnes n).coeff i = if i ≤ n then 1 else 0 := by sorry
