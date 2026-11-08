-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_integrable_rows_diagonal_L1_clipping
-- name    : AvramDividend.Classical.avram_bv_residual10_integrable_rows_diagonal_L1_clipping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:10:31.390552+00:00
-- url     : https://prove2.me/theorems/591a6b86-04a3-47cf-ae72-bcb3f38e5fdd
-- title:
--   Original integrable rows admit diagonal physical-grid coefficient clipping with vanishing L1 tails
-- statement:
--   For genuinely integrable original physical-grid row sources f n and measurable coefficient rows a n, there exists a deterministic integer cutoff K n for each n such that the expected absolute discarded source falls below 1/(n+1). One applies the proved fixed-row original L1 clipping theorem at each n, then chooses its eventual threshold. This removes any need for a single cutoff valid uniformly across all n, but does not infer the untruncated sources are integrable or prove the original mesh/contact error tends to zero.
-- source:
--   AVRAM BV-RESIDUAL10 original finite-grid dominated convergence and diagonal physical-row localisation, 7 November 2026

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_integrable_original_grid_localisation_tail

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_bv_residual10_integrable_rows_diagonal_L1_clipping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (a : ℕ → Ω → ℕ → ℝ)
    (ha : ∀ n i, Measurable (fun ω => a n ω i))
    (f : ℕ → Ω → ℝ)
    (hfm : ∀ n, Measurable (f n))
    (hf : ∀ n, Integrable (f n) P) :
    ∃ K : ℕ → ℕ, ∀ n : ℕ,
      (∫ ω : Ω,
        if ω ∈ {z : Ω | ∀ i ∈ Finset.range (n + 1),
          abs (a n z i) ≤ (K n : ℝ)} then (0 : ℝ)
          else abs (f n ω) ∂P) < 1 / ((n : ℝ) + 1) := by sorry
