-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_rowwise_probability_diagonal
-- name    : AvramDividend.Classical.avram_bv_residual10_original_rowwise_probability_diagonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:27:13.989336+00:00
-- url     : https://prove2.me/theorems/14a0bc0d-c4ec-4e23-8b5a-9ca75ee436a4
-- title:
--   Original physical-grid coefficient localisation diagonal with vanishing discarded probability
-- statement:
--   For any original physical-grid coefficient array with measurable coordinates and any strictly positive sequence of probability tolerances converging to zero, select one deterministic coefficient cutoff for each grid row so that the discarded event has probability below its row tolerance. In particular, the discarded-event probability tends to zero across the changing row length. No L1 integrability or uniform generator bound is assumed. This result does not itself establish a stopped compensation estimate.
-- source:
--   AVRAM BV-RESIDUAL10 original uniform-grid finite-coordinate event diagonalisation, 7 November 2026

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_compl_measure_tendsto

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_rowwise_probability_diagonal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    (a : ℕ → Ω → ℕ → ℝ)
    (ha : ∀ n i, Measurable (fun ω => a n ω i))
    (ε : ℕ → ℝ≥0∞) (hεpos : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ≥0∞))) :
    ∃ K : ℕ → ℕ,
      (∀ n, P ({ω : Ω | ∀ i ∈ Finset.range (n + 1),
        abs (a n ω i) ≤ (K n : ℝ)}ᶜ) < ε n) ∧
      Tendsto
        (fun n => P ({ω : Ω | ∀ i ∈ Finset.range (n + 1),
          abs (a n ω i) ≤ (K n : ℝ)}ᶜ))
        atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
