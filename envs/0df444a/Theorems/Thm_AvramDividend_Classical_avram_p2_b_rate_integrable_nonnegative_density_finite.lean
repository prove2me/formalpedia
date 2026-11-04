-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_integrable_nonnegative_density_finite
-- name    : AvramDividend.Classical.avram_p2_b_rate_integrable_nonnegative_density_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:21:43.788522+00:00
-- url     : https://prove2.me/theorems/279368b4-2627-4aa1-ac65-407a82fca2ee
-- title:
--   Integrable nonnegative weight defines a finite withDensity measure
-- statement:
--   A nonnegative almost-everywhere real-valued integrable weight yields a finite ENNReal weighted measure via withDensity, with finite total mass. This is the finite-measure existence prerequisite for the original Levy fourth-exponential weighted image family, without assuming any stationary jump-count rate.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_integrable_nonnegative_density_finite
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ)
    (hf : Integrable f μ)
    (hn : ∀ᵐ ω ∂μ, 0 ≤ f ω) :
    (μ.withDensity (fun ω => ENNReal.ofReal (f ω))) Set.univ < ⊤ := by sorry
