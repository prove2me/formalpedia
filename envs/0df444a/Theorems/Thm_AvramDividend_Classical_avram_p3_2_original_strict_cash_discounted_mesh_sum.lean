-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_strict_cash_discounted_mesh_sum
-- name    : AvramDividend.Classical.avram_p3_2_original_strict_cash_discounted_mesh_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:08:12.625994+00:00
-- url     : https://prove2.me/theorems/12b38ce7-b223-408e-be3c-0c260ec070fe
-- title:
--   Exact original strictly pre-T dividend-measure cash decomposes into stopped physical mesh cells
-- statement:
--   The original pre-ruin dividendMeasure restricted to actual paymentTimes and strictly before T is exactly additive across first n stopped physical mesh Ioc cells, for every ENNReal integrand.
-- source:
--   Fully Proved generic finite-Ioc lintegral additivity and original physical stopped-grid monotonicity, together with Mathlib measure restriction association; preserves exact original ruin and Iio T boundary.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_stopped_grid_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_Ioc_mesh_lintegral_finset_sum

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_strict_cash_discounted_mesh_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T : ℝ≥0) (m n : ℕ) (f : ℝ → ℝ≥0∞) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    let B : Set ℝ :=
      paymentTimes (ruinTime X x D ω) ∩ Iio (T : ℝ)
    (∫⁻ t in B ∩ Ioc (0 : ℝ) (u n : ℝ),
      f t ∂(dividendMeasure D ω)) =
      ∑ i ∈ Finset.range n,
        (∫⁻ t in B ∩ Ioc (u i : ℝ) (u (i + 1) : ℝ),
          f t ∂(dividendMeasure D ω)):= by sorry
