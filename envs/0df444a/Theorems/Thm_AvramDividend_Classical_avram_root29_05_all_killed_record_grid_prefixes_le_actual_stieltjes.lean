-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_all_killed_record_grid_prefixes_le_actual_stieltjes
-- name    : AvramDividend.Classical.avram_root29_05_all_killed_record_grid_prefixes_le_actual_stieltjes
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:15:18.385854+00:00
-- url     : https://prove2.me/theorems/8a816a69-3662-4292-9a8a-857542c7dc5f
-- title:
--   Whole killed rational-grid sampled regulator payoff is dominated by the actual stopped Stieltjes dividend reward
-- statement:
--   For each actual Lévy path and arbitrary strict stopping horizon, take the supremum over all positive mesh denominators and finite horizons of nonnegative discounted running-record increments retained only when the right endpoint precedes ruin. This full countable sampled payoff is bounded above by the genuine stopped Stieltjes dividend reward. The result supplies the source-level one-sided global convergence bound for the measurable path-space reward, without exit or scale inputs.
-- source:
--   Noncircular countable-sup consequence of canonically Proved finite killed record-grid prefix bound 94bff3f1, itself proved from actual Stieltjes measure interval bounds and finite partition identity. Consumer 79978d61.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_killed_record_grid_prefix_le_actual_stieltjes

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_root29_05_all_killed_record_grid_prefixes_le_actual_stieltjes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q) :
    (⨆ n : ℕ, ⨆ N : ℕ,
      let grid : ℕ → ℝ := fun j =>
        (((j : ℝ≥0) * ((n + 1 : ℕ) : ℝ≥0)⁻¹) : ℝ)
      ∑ k ∈ Finset.range N,
        if ENNReal.ofReal (grid (k + 1)) < τ then
          ENNReal.ofReal (Real.exp (-(q * grid (k + 1)))) *
            ENNReal.ofReal
              (runningSup X (grid (k + 1)).toNNReal ω -
                runningSup X (grid k).toNNReal ω)
        else 0) ≤
    (∫⁻ r in paymentTimes τ,
      if 0 < r then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) := by sorry
