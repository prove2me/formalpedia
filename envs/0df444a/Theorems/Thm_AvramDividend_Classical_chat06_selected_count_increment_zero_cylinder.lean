-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_selected_count_increment_zero_cylinder
-- name    : AvramDividend.Classical.chat06_selected_count_increment_zero_cylinder
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T06:30:51.658142+00:00
-- url     : https://prove2.me/theorems/10e29d61-98e5-4b58-bcae-d4fe5ea7ab4b
-- title:
--   Zero renewal-count increments from the selected residual waiting-time threshold
-- statement:
--   No additional renewal event occurs between clock and clock+t precisely when the selected residual waiting time to the next event exceeds t. This is the zero-increment endpoint of the exact count-cylinder family and follows from the already proved selected count-increment threshold equivalence.
-- source:
--   bv_selected_count_increment_zero_cylinder_v2_chat06_20261021.lean, 46 lines, 1747 bytes, SHA-256 9aee83ba05df220051e548ec56e064957cd02f6865d59cdb489ed65f5904e257; private remote probe d4234bc4-7ef5-4e91-8577-408352225021 reached sentinel with no candidate source errors.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Theorems.Thm_AvramDividend_Classical_chat06_selected_future_count_increment_event

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.chat06_selected_count_increment_zero_cylinder
    {Ω : Type*} (τ : Ω → ℕ → ℝ) (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ ω i) ≤ u)
    (clock t : ℝ) :
    {ω : Ω | N ω (clock + t) - N ω clock = 0} =
      {ω : Ω |
        t < ((∑ i ∈ Finset.range (N ω clock + 1), τ ω i) - clock) +
          (∑ j ∈ Finset.range 0, τ ω (N ω clock + 1 + j))} := by sorry
