-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_expectation_filter_limits_of_terminal_limit
-- name    : AvramDividend.Classical.chat04_killed_expectation_filter_limits_of_terminal_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:46:19.533975+00:00
-- url     : https://prove2.me/theorems/089d8e8d-c0d5-4a59-83da-02d72a821ac4
-- title:
--   Two-sided filter-limit identity for history-killed scale expectations at time zero
-- statement:
--   At positive initial reserve, if terminal-only q-scale expectation converges to W(x) as time tends to zero, then the genuine history-killed expectation has both liminf and limsup equal to W(x) over the full time-zero neighbourhood filter. This packages unconditional Fatou lower bound and conditional limsup upper bound into the exact analytic continuity input for killed semigroup arguments.
-- source:
--   Exact proved import chain: positive-reserve filter Fatou lower bound 618ce98c and terminal-convergence limsup bridge ddcc828c, plus pinned Mathlib Filter.liminf_le_limsup. Next foundational target: terminal-only time-zero expectation convergence using local uniform L² estimates; then open killed harmonicity a885f0b3 and stopped two-sided exit 09663d0d.

import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_expectation_filter_fatou
import Theorems.Thm_AvramDividend_Classical_chat04_killed_expectation_limsup_le_of_terminal_limit
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Order.LiminfLimsup

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_killed_expectation_filter_limits_of_terminal_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x)
    (hterminal : Tendsto (fun t : ℝ≥0 => (∫⁻ ω,
        ({u : Ω | 0 ≤ x + X.X t u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P))
      (𝓝 0) (𝓝 (ENNReal.ofReal (W x)))) :
    Filter.liminf (fun t : ℝ≥0 => (∫⁻ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P)) (𝓝 0) =
      ENNReal.ofReal (W x) ∧
    Filter.limsup (fun t : ℝ≥0 => (∫⁻ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P)) (𝓝 0) =
      ENNReal.ofReal (W x) := by sorry
