-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_sum_sq_cube_le
-- name    : AaronsonAmbainis.Level.sum_sq_cube_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:54:41.320272+00:00
-- url     : https://prove2.me/theorems/03863878-66fc-4384-8b37-3527fa65e483
-- title:
--   Level: sum sq cube le
-- statement:
--   A power-mean inequality: `(∑ z²)^3 ≤ #s · (∑ |z|^3)^2` (Lemma 7.9 of the paper).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Median.lean#L62-L93
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Median.lean#L62-L93

import Mathlib
import Definitions.Def_AaronsonAmbainis_Level_Median
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset

theorem AaronsonAmbainis.Level.sum_sq_cube_le {α : Type*} (s : Finset α) (z : α → ℝ) :
    (∑ i ∈ s, z i ^ 2) ^ 3 ≤ (s.card : ℝ) * (∑ i ∈ s, |z i| ^ 3) ^ 2 := by sorry
