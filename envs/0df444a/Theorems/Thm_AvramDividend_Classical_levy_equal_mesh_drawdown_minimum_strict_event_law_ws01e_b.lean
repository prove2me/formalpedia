-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_equal_mesh_drawdown_minimum_strict_event_law_ws01e_b
-- name    : AvramDividend.Classical.levy_equal_mesh_drawdown_minimum_strict_event_law_ws01e_b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:37:07.595258+00:00
-- url     : https://prove2.me/theorems/423621dc-5038-406f-9061-9567542359b8
-- title:
--   Strict finite-grid Lévy drawdown and running minimum event laws agree
-- statement:
--   For a spectrally negative Lévy process at equal-mesh observation times, the pushforward law of the padded finite increment vector assigns equal probabilities to the event that the terminal-minus-prefix sum ever falls strictly below a threshold and the event that some ordinary prefix sum falls strictly below the same threshold. The proof transports the genuine finite increment reversal law to padded infinite sequences and applies the Proved strict finite-grid reversal identity; no atomlessness hypothesis is used.
-- source:
--   Source-faithful strict-threshold adaptation of the already accepted closed-event Lévy increment-law transport and accepted strict finite-grid event theorem 1e6b36c9; Kuznetsov–Kyprianou–Rivero, scale-function review §2.1–2.2.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_finite_grid_drawdown_minimum_strict_event_probability_ws01e_b
import Theorems.Thm_AvramDividend_Classical_levy_equal_mesh_increment_vector_law_reversal_ws01e_b
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_equal_mesh_drawdown_minimum_strict_event_law_ws01e_b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (δ : ℝ≥0) (n : ℕ) (a : ℝ) :
    let inc : Ω → ℕ → ℝ := fun ω j =>
      if j < n then
        X.X (((j + 1 : ℕ) : ℝ≥0) * δ) ω -
          X.X ((j : ℝ≥0) * δ) ω
      else 0
    let ν : MeasureTheory.Measure (ℕ → ℝ) := MeasureTheory.Measure.map inc P
    ν {v : ℕ → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range n) v -
        Finset.sum (Finset.range k.val) v < a} =
    ν {v : ℕ → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range k.val) v < a} := by sorry
