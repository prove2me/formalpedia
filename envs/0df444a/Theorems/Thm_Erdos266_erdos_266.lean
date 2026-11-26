-- Prove2me | Theorems.Thm_Erdos266_erdos_266
-- name    : Erdos266.erdos_266
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T03:05:55.463257+00:00
-- url     : https://prove2.me/theorems/2b016a44-3631-5f44-9f4a-20a380f32ea0
-- title:
--   Erdos266: erdos 266
-- statement:
--   **Erdős problem #266 / Stolarsky's conjecture, disproved** (Kovač–Tao),
--   derived from the construction.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Solution.lean#L35-L38
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Solution.lean#L35-L38

module
public import Definitions.Def_Erdos266
public import Definitions.Def_Erdos266_Solution
set_option autoImplicit false
@[expose] public section
public section
open Erdos266

theorem Erdos266.erdos_266 :
    ¬ ∀ (a : ℕ → ℕ), ((∀ n : ℕ, a n ≥ 1) ∧ Summable ((1 : ℝ) / a ·) →
      ∃ t ≥ (1 : ℕ), Irrational <| ∑' n, (1 : ℝ) / ((a n) + t)) := by sorry
