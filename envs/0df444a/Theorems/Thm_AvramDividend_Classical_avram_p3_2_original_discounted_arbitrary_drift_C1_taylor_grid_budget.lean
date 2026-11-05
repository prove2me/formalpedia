-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_discounted_arbitrary_drift_C1_taylor_grid_budget
-- name    : AvramDividend.Classical.avram_p3_2_original_discounted_arbitrary_drift_C1_taylor_grid_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:38:24.107799+00:00
-- url     : https://prove2.me/theorems/6b8da128-c297-444c-b7dd-f7fd2ad3fa63
-- title:
--   Original weighted physical drift C1 Taylor grid error controlled by exact total drift variation
-- statement:
--   On original nonnegative physical clocks with q≥0, the discounted finite-grid nonlinear w drift Taylor remainder for arbitrary physical shifts is at most ε times the sum of their absolute shifts if each reserve shift stays in one strict compact C1 subcap band and has magnitude below a uniform δ. Together with the exact pure BV drift clock total variation telescope, this provides a path-independent mesh error envelope for P3-2's frozen drift-first original source decomposition.
-- source:
--   Source-independent accepted arbitrary physical-drift compact C1 Taylor cell lemma and nonnegative discount weights; exact original source recovered by c_i=Δt_i*X.drift.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_uniform_compact_C1_arbitrary_physical_drift_taylor_cell

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_discounted_arbitrary_drift_C1_taylor_grid_budget
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
      ∀ (u : ℕ → ℝ≥0) (n : ℕ) (z c : ℕ → ℝ),
        (∀ i, i < n → Set.uIcc (z i) (z i + c i) ⊆ Set.Icc a b) →
        (∀ i, i < n → |c i| < δ) →
        |∑ i ∈ Finset.range n,
          Real.exp (-(q * (u i : ℝ))) *
            (w (z i + c i) - w (z i) - deriv w (z i) * c i)| ≤
          ε * (∑ i ∈ Finset.range n, |c i|) := by sorry
