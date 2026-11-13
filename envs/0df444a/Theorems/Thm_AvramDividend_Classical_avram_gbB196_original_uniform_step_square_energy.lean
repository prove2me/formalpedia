-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB196_original_uniform_step_square_energy
-- name    : AvramDividend.Classical.avram_gbB196_original_uniform_step_square_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T22:38:35.106307+00:00
-- url     : https://prove2.me/theorems/7ecba251-cc63-4f6a-8f5d-04134ac84b30
-- title:
--   One original uniform step coefficient square energy integrates to cell-width weighted square sum
-- statement:
--   For bounded, strongly measurable coefficients on a finite uniform time grid, the integrated expected square of the actual step process equals cell width times the sum of expected coefficient squares.
-- source:
--   Avram Gaussian B: deterministic one-grid specialization of proved two-grid time covariance energy and finite block regrouping; used in gbB66 and gbB83.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB196_original_uniform_step_square_energy
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (n m : ℕ) (hn : 0 < n)
    (G : ℕ → ℕ → Ω → ℝ)
    (hG : ∀ a i, StronglyMeasurable (G a i))
    (hBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ a i ω, |G a i ω| ≤ B) :
    let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 1)
    let K : ℕ → ℝ → Ω → ℝ := fun k t ω =>
      let δ : ℝ≥0 := (n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * δ
      (Finset.range (k + 1)).sum (fun i =>
        if (s i : ℝ) ≤ t ∧ t < ((s i + δ : ℝ≥0) : ℝ)
        then G k i ω else 0)
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      (∫ ω, (K m t ω) ^ 2 ∂P) ∂volume) =
      Δ * (Finset.range (m + 1)).sum (fun i =>
        ∫ ω, (G m i ω) ^ 2 ∂P) := by sorry
