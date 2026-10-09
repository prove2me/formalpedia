-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_jump_tail_density_total_mass
-- name    : AvramDividend.Classical.positive_jump_tail_density_total_mass
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T16:12:12.277738+00:00
-- url     : https://prove2.me/theorems/643537e3-486f-4c7d-abb9-3b482377dade
-- title:
--   Total mass of the positive tail-density measure equals the first moment
-- statement:
--   For any nonnegative jump-magnitude measure μ, the measure on positive reserves with density t↦μ((t,∞)) has total mass ∫z μ(dz), potentially infinite. This is Tonelli's layer-cake identity ∫_0^∞μ((t,∞))dt=∫_0^∞zμ(dz), with the zero and endpoint conventions made explicit. Once μ is discounted by Esscher factor exp(-φz), this theorem converts the already-Proved discounted first-moment bound directly into the strict total-mass bound required to sum the geometric root-shifted renewal measure. The proof uses pinned Mathlib Measure.withDensity_apply, lintegral_indicator_one, lintegral_lintegral_swap and Real.volume_Ioo.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_lintegral_swap, MeasureTheory.lintegral_indicator_one, MeasureTheory.Measure.withDensity_apply, Real.volume_Ioo.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_jump_tail_density_total_mass
    (μ : Measure ℝ≥0) :
    ((volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun t : ℝ => μ {z : ℝ≥0 | t < (z : ℝ)})) Set.univ =
      ∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ := by sorry
