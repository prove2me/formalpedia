-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflected_excursion_height_max_forces_no_immediate_negative_increments
-- name    : AvramDividend.Classical.reflected_excursion_height_max_forces_no_immediate_negative_increments
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:18:12.254702+00:00
-- url     : https://prove2.me/theorems/a7538062-7d74-4546-bf62-e133b9300e85
-- title:
--   A pathwise excursion-height maximum forces a nonnegative-increment right neighbourhood after the hitting time
-- statement:
--   If a reflected drawdown R=S-Y with nondecreasing S attains a level x at a time T strictly before excursion lifetime ζ, and cannot exceed x during the remaining excursion, then on some entire right time interval after T the underlying process Y cannot have a strictly negative increment relative to Y(T). Contraposition isolates the deterministic obstruction to any excursion having exact height x: a fresh post-hitting path must fail downward regularity. This lemma neither assumes nor proves the excursion strong Markov property.
-- source:
--   Kuznetsov, Kyprianou and Rivero (2013), The Theory of Scale Functions for Spectrally Negative Lévy Processes, Section 2.3, absence of atoms of excursion height.

import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith


open Set
open scoped NNReal

theorem AvramDividend.Classical.reflected_excursion_height_max_forces_no_immediate_negative_increments
    (S Y : ℝ≥0 → ℝ) (T ζ x : ℝ≥0)
    (hT : T < ζ)
    (hS : Monotone S)
    (hHit : S T - Y T = (x : ℝ))
    (hNoExceed : ∀ t : ℝ≥0, T ≤ t → t < ζ →
      S t - Y t ≤ (x : ℝ)) :
    ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ s : ℝ≥0, s < ε → Y T ≤ Y (T + s) := by sorry
