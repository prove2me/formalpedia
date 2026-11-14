-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb25_original_restricted_negative_mark_guard_integral_const
-- name    : AvramDividend.Classical.avram_bvb25_original_restricted_negative_mark_guard_integral_const
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:53:14.163202+00:00
-- url     : https://prove2.me/theorems/aa8daed6-e341-4d64-82a2-1e4d884cf961
-- title:
--   Original Lévy negative-mark restricted measure integrates the full negative-mark guard constant without losing intensity
-- statement:
--   When integrating against the original spectrally negative Lévy measure restricted to strictly negative marks, a mark-fibre equal to a fixed real value on all negative marks and zero elsewhere integrates to that value multiplied by the complete original negative-mark intensity, with the exact toReal convention of the source marked K compensator. This is a reusable full-measure, boundary-contact integration fact needed after reducing the original stopped K integrand pointwise. The factor retains all original negative marks rather than replacing the Lévy measure by a surrogate rate.
-- source:
--   Pinned Mathlib ae_restrict_mem, integral_congr_ae, integral_const and Measure.restrict_apply_univ. Exact source negative mark restriction from ed067740.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb25_original_restricted_negative_mark_guard_integral_const
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) :
    (∫ z : ℝ, (if z < 0 then a else 0) ∂(X.ν.restrict (Iio (0 : ℝ)))) =
      a * (X.ν (Iio (0 : ℝ))).toReal := by sorry
