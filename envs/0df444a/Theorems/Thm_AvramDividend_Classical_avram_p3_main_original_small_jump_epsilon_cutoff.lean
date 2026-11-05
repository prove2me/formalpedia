-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_small_jump_epsilon_cutoff
-- name    : AvramDividend.Classical.avram_p3_main_original_small_jump_epsilon_cutoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:40:55.569197+00:00
-- url     : https://prove2.me/theorems/f53aa65a-fcca-46ef-a1dd-48ef52044379
-- title:
--   Original BV negative-jump total small-mark mass has positive epsilon cutoff
-- statement:
--   For actual absolutely summable original BV Lévy negative-source jump magnitudes indexed by original time marks, obtain a positive threshold δ such that the total absolute magnitude of all source jumps strictly smaller than δ is under ε. Uses finite exceptional source-times, removes zero marks, selects positive finite cutoff and compares source-indexed tsum tails; the proof is an unconditional deterministic transfer valid pathwise on P3-A's original full-measure BV event.
-- source:
--   Original P3-A absolute-jump summability; public Proved original finite-tail 30e786d4, zero-mark bridge publication from private Proved cd2bddc4, nonzero finite-cutoff bridge publication from private Proved 182e334a, small-mark domination e3b32d24, subtype-index indicator equality 776632f2; P3-D interface obligation 5 and canonical a19d8b28.

import Mathlib
open scoped BigOperators

theorem AvramDividend.Classical.avram_p3_main_original_small_jump_epsilon_cutoff
    {ι : Type*} [DecidableEq ι] (j : ι → ℝ)
    (hj : Summable (fun i => |j i|))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      (∑' i : ι, if |j i| < δ then |j i| else 0) < ε := by sorry
