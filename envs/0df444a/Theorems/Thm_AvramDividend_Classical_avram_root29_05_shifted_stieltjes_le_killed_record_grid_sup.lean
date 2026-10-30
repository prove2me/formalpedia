-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_stieltjes_le_killed_record_grid_sup
-- name    : AvramDividend.Classical.avram_root29_05_shifted_stieltjes_le_killed_record_grid_sup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:41:41.315953+00:00
-- url     : https://prove2.me/theorems/33552272-4174-40cf-9c24-6bd4269813d5
-- title:
--   True future Stieltjes killed reward bounded by sampled shifted cashflows
-- statement:
--   For each actual spectrally negative Lévy path and each finite future shift, the genuine killed Stieltjes dividend integral of its future running-supremum regulator is bounded above by the supremum of finite rational sampled discounted record increments, for arbitrary stopping clock and discount parameter.
-- source:
--   Apply the Proved shifted genuine Stieltjes killed-mesh prefix identity to the generic positive-time interval exhaustion, then the generic pathwise Fatou lower-integral bound. This is the original Stieltjes mass with the actual future-increment process, independent of Markov renewal.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_killed_mesh_fatou_lower_integral
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_positive_time_rational_prefix_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_killed_mesh_prefix_integral_identity

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal BigOperators Classical

/-- The true shifted future Stieltjes killed reward is at most the supremum
of its finite discounted future-record cash meshes, pathwise. -/

theorem AvramDividend.Classical.avram_root29_05_shifted_stieltjes_le_killed_record_grid_sup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (age : ℝ≥0)
    (q : ℝ) (τ : ℝ≥0∞) :
    let M : ℝ≥0 → ℝ := fun v =>
      sSup ((fun w : ℝ≥0 => X.X (age + w) ω - X.X age ω) '' Icc 0 v)
    let μ : Measure ℝ := dividendMeasure (fun r (_ : Ω) => M r) ω
    (∫⁻ r : ℝ,
      if 0 < r then
        if ENNReal.ofReal r < τ then
          ENNReal.ofReal (Real.exp (-(q * r))) else 0
      else 0 ∂μ) ≤
    ⨆ n : ℕ, ⨆ N : ℕ,
      (let grid : ℕ → ℝ := fun j => (j : ℝ) / ((n : ℝ) + 1)
       ∑ k ∈ Finset.range N,
         (if ENNReal.ofReal (grid (k + 1)) < τ then
           ENNReal.ofReal (Real.exp (-(q * grid (k + 1)))) else 0) *
         ENNReal.ofReal (M (grid (k + 1)).toNNReal -
           M (grid k).toNNReal)) := by sorry
