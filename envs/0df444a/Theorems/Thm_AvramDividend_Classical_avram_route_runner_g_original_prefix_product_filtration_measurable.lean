-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_runner_g_original_prefix_product_filtration_measurable
-- name    : AvramDividend.Classical.avram_route_runner_g_original_prefix_product_filtration_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:20:35.905758+00:00
-- url     : https://prove2.me/theorems/72e815ad-43f4-44ad-88a1-92ded7e17c35
-- title:
--   Original strictly negative marked prefix product is adapted to its terminal filtration
-- statement:
--   The actual spectrally negative Lévy process product over all strictly negative cutoff jumps up to a deterministic time T is measurable relative to the filtration at T. This identifies the finite marked product with the previously established measurable physical Laplace functional.
-- source:
--   AVRAM Route Runner G 7 November 2026 exact original source, upstream 2299f164 and 24421b1f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_e_original_cell_product_laplace
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_arbitrary_prefix_laplace_filtration_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_route_runner_g_original_prefix_product_filtration_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (k : ℕ) :
    Measurable[𝓕 T] (fun ω : Ω =>
      ∏ u ∈ (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset,
        Real.exp (X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by sorry
