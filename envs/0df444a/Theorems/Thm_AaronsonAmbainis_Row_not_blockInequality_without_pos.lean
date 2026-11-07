-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_not_blockInequality_without_pos
-- name    : AaronsonAmbainis.Row.not_blockInequality_without_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:25:42.091342+00:00
-- url     : https://prove2.me/theorems/41d6ba4a-68ce-421a-8693-ce535a608806
-- title:
--   Row: not block Inequality without pos
-- statement:
--   `BlockInequality` with the hypothesis `0 < m` deleted is false.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/HypothesisCheck.lean#L18-L42
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/HypothesisCheck.lean#L18-L42

import Definitions.Def_AaronsonAmbainis_Row_Main
import Definitions.Def_AaronsonAmbainis_Row_HypothesisCheck
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset

theorem AaronsonAmbainis.Row.not_blockInequality_without_pos :
    ¬ (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
        HasDegreeLE f d →
      ∀ (x : Cube ι) (β : Type) [Fintype β] (S : β → Finset ι) (N m : ℕ),
        (∀ i, (univ.filter fun b : β => i ∈ S b).card ≤ N) →
        (N : ℝ) * (1 - Real.cos (Real.pi / (m : ℝ))) ≤ 2 →
        ∑ b, |f x - f (flipSet x (S b))| ≤ 4 * (d : ℝ) ^ 2 * (m : ℝ) ^ 2) := by sorry
