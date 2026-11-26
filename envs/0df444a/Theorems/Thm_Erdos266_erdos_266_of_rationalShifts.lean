-- Prove2me | Theorems.Thm_Erdos266_erdos_266_of_rationalShifts
-- name    : Erdos266.erdos_266_of_rationalShifts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:31:27.948068+00:00
-- url     : https://prove2.me/theorems/68e36131-3845-4ace-8820-9870ce05c24f
-- title:
--   Erdos266: erdos 266 of rational Shifts
-- statement:
--   From any strictly increasing positive sequence with the rational-shifts
--   property, the negative answer to Erdős problem #266 follows.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Glue.lean#L51-L74
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Glue.lean#L51-L74

module
public import Mathlib
public import Definitions.Def_Erdos266_Glue
set_option autoImplicit false
@[expose] public section
public section
open Erdos266

theorem Erdos266.erdos_266_of_rationalShifts
    (h : ∃ a : ℕ → ℕ, StrictMono a ∧ a 0 ≥ 1 ∧ RationalShifts a) :
    ¬ ∀ (a : ℕ → ℕ), ((∀ n : ℕ, a n ≥ 1) ∧ Summable ((1 : ℝ) / a ·) →
      ∃ t ≥ (1 : ℕ), Irrational <| ∑' n, (1 : ℝ) / ((a n) + t)) := by sorry
