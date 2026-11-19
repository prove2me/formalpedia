-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_zero_or_strict_canonical_cash_mesh_error_zero
-- name    : AvramDividend.Classical.avram_jump6_B_original_zero_or_strict_canonical_cash_mesh_error_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:29:07.408719+00:00
-- url     : https://prove2.me/theorems/e69e47d2-f03f-4e27-9c1e-9cb6676eee22
-- title:
--   Original canonical stopped cash mesh error vanishes at zero or strictly before true ruin
-- statement:
--   For the original same-process stopped dividend Stieltjes measure and canonical clipped physical mesh, the real discounted cash quadrature error converges to zero at any nonnegative horizon t bounded by n provided t is zero or lies strictly before true ruin. The strict case reuses the public source-faithful zero-error theorem; at t=0 every Ioc cell and rightLimit dividend increment vanishes. This handles the stopped clock zero branch necessary in mixed infinite-activity source limits without weakening the path or cap conditions.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_clipped_stieltjes_cash_discount_error_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_grid_reaches_bounded_clock_every_mesh
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_zero_or_strict_canonical_cash_mesh_error_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (t : ℝ≥0) (n : ℕ) (ht : t ≤ (n : ℝ≥0))
    (hClock : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    let N : ℕ → ℕ := fun j => (n + 1) * (j + 1)
    let v : ℕ → ℕ → ℝ≥0 := fun j i =>
      min ((i : ℝ≥0) * ((1 : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0))) t
    Tendsto (fun j : ℕ =>
      ∑ i ∈ Finset.range (N j),
        ((∫⁻ r in paymentTimes (ruinTime X x D ω) ∩
            Ioc (v j i : ℝ) (v j (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * r)))
            ∂(dividendMeasure D ω)).toReal -
          Real.exp (-(q * (v j (i + 1) : ℝ))) *
            (rightLimit D (v j (i + 1)) ω - rightLimit D (v j i) ω)))
      atTop (𝓝 (0 : ℝ)) := by sorry
