-- Prove2me | Theorems.Thm_AllOnesLab_boundary_one
-- name    : AllOnesLab.boundary_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:56:49.9668+00:00
-- url     : https://prove2.me/theorems/c590a3ab-a4df-52bc-9f68-d97bae91d65c
-- title:
--   All Ones Lab: boundary one
-- statement:
--   The boundary case `n = 1` genuinely fails: `X + 1` is irreducible but `X² + X` is not.
--
--   Source: https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Main.lean#L25-L26
-- source:
--   https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Main.lean#L25-L26

import Definitions.Def_AllOnesLab_Hard
import Definitions.Def_AllOnesLab_Main
set_option autoImplicit true
open Polynomial
open AllOnesLab

theorem AllOnesLab.boundary_one : Irreducible (allOnes 1) ∧ ¬ Irreducible (allOnesP 1) := by sorry
