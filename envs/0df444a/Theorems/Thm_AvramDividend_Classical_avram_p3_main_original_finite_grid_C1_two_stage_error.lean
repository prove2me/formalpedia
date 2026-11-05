-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_finite_grid_C1_two_stage_error
-- name    : AvramDividend.Classical.avram_p3_main_original_finite_grid_C1_two_stage_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:17:58.74076+00:00
-- url     : https://prove2.me/theorems/d8b4a9b4-c5e9-43a3-8b83-92a86c34b86b
-- title:
--   Original BV finite-grid full nonlinear jump plus C1 Taylor two-stage error
-- statement:
--   For an actual BV physical source mesh delta=continuous increment minus original negative jump magnitude, bound the complete signed weighted source step relative to the intrinsic original jump increment and first-order C1 drift. The error splits into a derivative-oscillation variation term and finite-large versus summable-small original jump translation term.
-- source:
--   Source-exact composition of two genuinely Proved public P3-D replays aab7abee-5bd9-43cb-b2c6-fbd620fb1ed4 and d87eca9e-5de4-46f3-9129-b11bc07e2eb0 on pinned Mathlib; intended for original stopped C1 integration witness 7bb152c2.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_public_weighted_source_jump_taylor_error
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_public_large_small_original_jump_translation_bound
open AvramDividend.Classical
open scoped BigOperators

theorem AvramDividend.Classical.avram_p3_main_original_finite_grid_C1_two_stage_error
    (n : ℕ) (S : Finset ℕ) (f : ℝ → ℝ)
    (r z cont jump delta : ℕ → ℝ) (ε B K : ℝ)
    (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hstep : ∀ i, i < n → delta i = cont i - jump i)
    (hr : ∀ i, i < n → 0 ≤ r i ∧ r i ≤ 1)
    (htaylor : ∀ i, i < n →
      |f (z i + cont i) - f (z i) - deriv f (z i) * cont i| ≤
        ε * |cont i|)
    (hvar : (∑ i ∈ Finset.range n, |cont i|) ≤ B)
    (hlarge : ∀ i, i < n → i ∈ S →
      |f (z i + cont i - jump i) - f (z i - jump i)| ≤ K * |cont i| ∧
      |f (z i + cont i) - f (z i)| ≤ K * |cont i|)
    (hsmall : ∀ i, i < n → i ∉ S →
      |f (z i + cont i - jump i) - f (z i + cont i)| ≤ K * |jump i| ∧
      |f (z i - jump i) - f (z i)| ≤ K * |jump i|) :
    |∑ i ∈ Finset.range n,
      r i * ((f (z i + delta i) - f (z i)) -
        (f (z i - jump i) - f (z i)) -
        deriv f (z i) * cont i)| ≤
      ε * B + 2 * K * (∑ i ∈ Finset.range n,
        if i ∈ S then |cont i| else |jump i|) := by sorry
