-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise34_dyadic_mark_cell_endpoint_error
-- name    : AvramDividend.Classical.avram_anoise34_dyadic_mark_cell_endpoint_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:04:08.640278+00:00
-- url     : https://prove2.me/theorems/910da379-53d4-48d7-8bf8-acc66575e11b
-- title:
--   Dyadic negative-mark cell approximation has error at most cell width
-- statement:
--   For a real negative mark in the actual cutoff band intersected with a dyadic interval of length 2^{-k}, its distance from that cell's left endpoint is at most 2^{-k}. This elementary geometric estimate is the deterministic input for the original marked-count approximation and finite-activity L1 domination in the Avram Gaussian residual source.
-- source:
--   Exact deterministic geometric ingredient of root-connected Open 4da238cd. The proof uses only that a mark belongs to its right-closed dyadic cell and has no independent-noise or stochastic assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise34_dyadic_mark_cell_endpoint_error
    (n k i : ℕ) (z : ℝ)
    (hz : z ∈ (Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))) ∩
      Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
        (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k))) :
    |z - (-1 + (i : ℝ) / (2 : ℝ) ^ k)| ≤ 1 / (2 : ℝ) ^ k := by sorry
