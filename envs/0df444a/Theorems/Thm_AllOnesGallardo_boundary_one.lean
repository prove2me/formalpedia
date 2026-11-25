-- Prove2me | Theorems.Thm_AllOnesGallardo_boundary_one
-- name    : AllOnesGallardo.boundary_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:58:47.213916+00:00
-- url     : https://prove2.me/theorems/0a7d0bdd-827f-559a-be72-f8affd751656
-- title:
--   All Ones Gallardo: boundary one
-- statement:
--   The boundary case `n = 1` genuinely fails: `X + 1` is irreducible but `X² + X` is not.
--
--   Source: https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/Solution.lean#L44-L45
-- source:
--   https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/Solution.lean#L44-L45

import Definitions.Def_AllOnesLab
import Definitions.Def_AllOnesComparator_Solution
import Theorems.Thm_AllOnesLab_boundary_one

set_option autoImplicit true
open Polynomial
open AllOnesGallardo

theorem AllOnesGallardo.boundary_one : Irreducible (allOnes 1) ∧ ¬ Irreducible (allOnesP 1) := by sorry
