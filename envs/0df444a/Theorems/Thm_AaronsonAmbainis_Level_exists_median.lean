-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_exists_median
-- name    : AaronsonAmbainis.Level.exists_median
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:54:26.883211+00:00
-- url     : https://prove2.me/theorems/cca82036-fea3-41f5-bbfe-4d8be9c16ce1
-- title:
--   Level: exists median
-- statement:
--   A real function on a nonempty finite type has a median (Lemma 7.8 of the paper).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Median.lean#L20-L59
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Median.lean#L20-L59

import Mathlib
import Definitions.Def_AaronsonAmbainis_Level_Median
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset

theorem AaronsonAmbainis.Level.exists_median {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) :
    ∃ m : ℝ, Fintype.card X ≤ 2 * (univ.filter (fun x => f x ≤ m)).card ∧
      Fintype.card X ≤ 2 * (univ.filter (fun x => m ≤ f x)).card := by sorry
