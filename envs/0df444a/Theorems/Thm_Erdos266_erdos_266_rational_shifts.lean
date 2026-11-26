-- Prove2me | Theorems.Thm_Erdos266_erdos_266_rational_shifts
-- name    : Erdos266.erdos_266_rational_shifts
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T03:03:07.537666+00:00
-- url     : https://prove2.me/theorems/261b1985-de37-5185-885e-5ac714778da3
-- title:
--   Erdos266: erdos 266 rational shifts
-- statement:
--   **The Kovač–Tao construction** (Theorem 2.11 of [KoTa24]).
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Solution.lean#L27-L31
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Solution.lean#L27-L31

module
public import Definitions.Def_Erdos266
public import Definitions.Def_Erdos266_Solution
set_option autoImplicit false
@[expose] public section
public section
open Erdos266

theorem Erdos266.erdos_266_rational_shifts :
    ∃ a : ℕ → ℕ, StrictMono a ∧ a 0 ≥ 1 ∧
      (∀ t : ℚ, (¬ ∃ n : ℕ, t = -(a n)) →
        (∃ q : ℚ, HasSum (fun n : ℕ => ((1 : ℝ) / ((a n) + t))) q)) := by sorry
