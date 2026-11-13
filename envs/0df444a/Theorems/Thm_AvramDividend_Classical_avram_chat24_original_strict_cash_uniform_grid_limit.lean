-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_original_strict_cash_uniform_grid_limit
-- name    : AvramDividend.Classical.avram_chat24_original_strict_cash_uniform_grid_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:30:07.705886+00:00
-- url     : https://prove2.me/theorems/0c66e93d-708c-4326-a922-32c6d2a1e95a
-- title:
--   Original strict Stieltjes cash uniform-grid limit
-- statement:
--   Source-faithful analytic child of actual limit target 8ee5bfc7-c7d8-44b0-904f-a68e4becd13f. The actual original strict dividend cash on [0,B) is the limit of left-discounted sums on the explicit n+1-cell uniform grid, preserving the time-zero atom and excluding the right atom at B. No convergence assumption is added.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_chat24_original_strict_cash_uniform_grid_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (B : ℝ≥0) :
    Tendsto (fun n : ℕ =>
      let N : ℕ := n + 1
      let u : ℕ → ℝ≥0 := fun i => B * (i : ℝ≥0) / (N : ℝ≥0)
      ∑ i ∈ Finset.range N, Real.exp (-(q * (u i : ℝ))) *
        (D (u (i + 1)) ω - D (u i) ω)) atTop
      (nhds ((∫⁻ t in Ico (0 : ℝ) (B : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)) := by sorry
