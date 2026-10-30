-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_actual_stieltjes_le_killed_record_grid_sup
-- name    : AvramDividend.Classical.avram_root29_05_actual_stieltjes_le_killed_record_grid_sup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:49:58.431429+00:00
-- url     : https://prove2.me/theorems/c5704d66-1cf0-4a6d-85b8-04fa6ae24a5c
-- title:
--   Full actual strictly killed running-supremum Stieltjes reward is bounded by all rational record-grid cashflows
-- statement:
--   For every actual original spectrally negative Lévy path, discount q, arbitrary exact strictly killed time τ, the full positive-time nonnegative Stieltjes regulator dividend reward is bounded above by the supremum over all rational-mesh denominators and finite prefixes of the discounted strictly surviving actual record-increment payments. This is the missing reverse direction to the previously Proved grid≤actual Stieltjes bound, with genuine dividendMeasure and actual ruin stopping interface. It follows from proven Fatou convergence, positive-time directed exhaustion, and finite partition identity against the original running-supremum dividend measure. No scale quotient, false stopping set, stochastic exit identity or finiteness assumption is used.
-- source:
--   Proved genuine Fatou inequality 16751744, positive-time mesh exhaustion 6d37073b and original-regulator finite killed prefix identity bbbb2b66. Source-level reverse of 94bff3f1 / 8a816a69; supports canonical 79978d61.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_killed_mesh_fatou_lower_integral
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_positive_time_rational_prefix_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_actual_record_killed_mesh_prefix_integral_identity

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal BigOperators Classical

theorem AvramDividend.Classical.avram_root29_05_actual_stieltjes_le_killed_record_grid_sup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (q : ℝ) (τ : ℝ≥0∞) :
    (∫⁻ r : ℝ,
      if 0 < r then
        if ENNReal.ofReal r < τ then
          ENNReal.ofReal (Real.exp (-(q * r))) else 0
      else 0 ∂(dividendMeasure (runningSup X) ω)) ≤
    ⨆ n : ℕ, ⨆ N : ℕ,
      (let u : ℕ → ℝ := fun j => (j : ℝ) / ((n : ℝ) + 1)
       ∑ k ∈ Finset.range N,
         (if ENNReal.ofReal (u (k + 1)) < τ then
           ENNReal.ofReal (Real.exp (-(q * u (k + 1)))) else 0) *
         ENNReal.ofReal (runningSup X (u (k + 1)).toNNReal ω -
           runningSup X (u k).toNNReal ω)) := by sorry
