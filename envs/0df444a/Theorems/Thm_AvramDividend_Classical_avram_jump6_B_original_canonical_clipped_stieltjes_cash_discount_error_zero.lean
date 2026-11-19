-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_clipped_stieltjes_cash_discount_error_zero
-- name    : AvramDividend.Classical.avram_jump6_B_original_canonical_clipped_stieltjes_cash_discount_error_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T20:31:38.701775+00:00
-- url     : https://prove2.me/theorems/7237a369-3d8e-4afe-ac16-704c2250ac19
-- title:
--   Actual original strict-preruin clipped physical-grid dividend discount error tends to zero
-- statement:
--   At any original path with bounded strictly pre-ruin stopped clock t, the actual fixed canonical uniform physical-grid clipping and true original paymentTimes Ioc cell integral, with right-end discounted rightLimit D increments, have vanishing total real discount error. Uses the original admissible dividend strategy and no jump-intensity assumption. The all-index canonical grid cover, original uniform cell widths, pre-ruin support and finite path mass bound are established from genuine source data, then existing Proved true-paymentTimes mesh theorem transfers the limit. This is an essential strict-clock payment budget component. Publication preamble restricts to available declarations; proof import remains separately remote validated.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_grid_reaches_bounded_clock_every_mesh
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_canonical_clipped_stieltjes_cash_discount_error_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (t : ℝ≥0) (n : ℕ) (ht : t ≤ (n : ℝ≥0))
    (hStrict : (t : ℝ≥0∞) < ruinTime X x D ω) :
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
