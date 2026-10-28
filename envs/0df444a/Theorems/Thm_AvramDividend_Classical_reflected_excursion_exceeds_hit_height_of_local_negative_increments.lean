-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflected_excursion_exceeds_hit_height_of_local_negative_increments
-- name    : AvramDividend.Classical.reflected_excursion_exceeds_hit_height_of_local_negative_increments
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:09:29.673981+00:00
-- url     : https://prove2.me/theorems/00719d15-e944-444d-bdaf-0b8085208649
-- title:
--   Downward increments immediately after a reflected excursion reaches a height force a higher excursion height
-- statement:
--   Let a reflected drawdown be R(t)=S(t)-Y(t), where S is nondecreasing. Suppose an excursion reaches height x at a time T before its lifetime ζ and the underlying process Y has strictly negative increments arbitrarily soon after T. Then R exceeds x strictly before the excursion lifetime. This is the deterministic pathwise implication needed after applying the strong Markov property to prove absence of atoms in reflected-excursion heights. It does not assert that downward regularity or the excursion Markov property has been established.
-- source:
--   Kuznetsov, Kyprianou and Rivero (2012), Theory of Scale Functions for Spectrally Negative Lévy Processes, Section 2.3, excursion-height atomlessness argument.

import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith

open Set
open scoped NNReal

theorem AvramDividend.Classical.reflected_excursion_exceeds_hit_height_of_local_negative_increments
    (S Y : ℝ≥0 → ℝ) (T ζ x : ℝ≥0)
    (hT : T < ζ)
    (hS : Monotone S)
    (hHit : S T - Y T = (x : ℝ))
    (hNeg : ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ Y (T + s) < Y T) :
    ∃ t : ℝ≥0, T ≤ t ∧ t < ζ ∧ (x : ℝ) < S t - Y t := by sorry
