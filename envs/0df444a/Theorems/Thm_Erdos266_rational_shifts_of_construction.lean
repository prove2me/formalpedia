-- Prove2me | Theorems.Thm_Erdos266_rational_shifts_of_construction
-- name    : Erdos266.rational_shifts_of_construction
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:37:47.711974+00:00
-- url     : https://prove2.me/theorems/d9414260-dd7f-538c-8b80-3cc14e8eee8a
-- title:
--   Erdos266: rational shifts of construction
-- statement:
--   **Milestone.**  The full Kovač–Tao theorem (the remaining Challenge
--   `sorry`) now follows from the existence of a single sequence with rational
--   `f`-sums; constructing it is the business of Sections 7–8 of the paper.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Reduction.lean#L203-L210
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Reduction.lean#L203-L210

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Glue
public import Definitions.Def_Erdos266_Reduction
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
variable {a : ℕ → ℕ}

theorem Erdos266.rational_shifts_of_construction
    (h : ∃ a : ℕ → ℕ, StrictMono a ∧ 1 ≤ a 0 ∧
      ∀ i, 1 ≤ i → ∃ q : ℚ, HasSum (fun n => f i (a n)) (q : ℝ)) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ a 0 ≥ 1 ∧
      (∀ t : ℚ, (¬ ∃ n : ℕ, t = -(a n)) →
        (∃ q : ℚ, HasSum (fun n : ℕ => ((1 : ℝ) / ((a n) + t))) q)) := by sorry
