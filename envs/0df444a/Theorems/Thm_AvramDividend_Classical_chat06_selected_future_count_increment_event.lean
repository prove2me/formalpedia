-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_selected_future_count_increment_event
-- name    : AvramDividend.Classical.chat06_selected_future_count_increment_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T18:06:31.848063+00:00
-- url     : https://prove2.me/theorems/8bf6e0fa-fd2e-41ad-9aa9-98e3b8496187
-- title:
--   Future renewal count-increment event equals a selected residual waiting-time prefix event
-- statement:
--   For an arbitrary sample-path indexed renewal count satisfying the exact arrival threshold law, the event of at least m+1 additional claims between clock and clock+t equals the event that the random selected residual waiting time, plus the next m waiting times, is at most t. No independence is assumed here. The identity is pathwise and is designed for use with the accepted countwise residual/future joint law to prove increment events independent of past observations.
-- source:
--   bv_selected_future_count_increment_event_chat06_20261021.lean, 41 lines, 1802 bytes, SHA-256 037658eb4332f0485aade239fd5edba0d6ab485bc84204d1a96b03c89aceb220; private remote job 5a5d80a3-c742-42c9-842c-194f9e0ca44c passed sentinel with zero source errors.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.chat06_selected_future_count_increment_event
    {Ω : Type*} (τ : Ω → ℕ → ℝ) (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ ω i) ≤ u)
    (clock t : ℝ) (m : ℕ) :
    {ω : Ω | m < N ω (clock + t) - N ω clock} =
      {ω : Ω |
        ((∑ i ∈ Finset.range (N ω clock + 1), τ ω i) - clock) +
          (∑ j ∈ Finset.range m, τ ω ((N ω clock + 1) + j)) ≤ t} := by sorry
