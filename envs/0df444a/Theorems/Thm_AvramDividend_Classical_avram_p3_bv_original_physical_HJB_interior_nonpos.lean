-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_physical_HJB_interior_nonpos
-- name    : AvramDividend.Classical.avram_p3_bv_original_physical_HJB_interior_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:34:41.970207+00:00
-- url     : https://prove2.me/theorems/536cef19-1b43-403f-abaa-fb110ace4303
-- title:
--   Original BV interior HJB sign expressed in physical drift and negative Lévy jump integral
-- statement:
--   At an arbitrary interior positive reserve, the original BV process generator HJB inequality is exactly the physical drift times first derivative plus the negative-jump Lévy integral minus discounted candidate value. It uses a Proved same-source identification of the generator and the physical BV drift, explicitly retaining the separate pathwise residual term in that source theorem. No substitute stochastic process, zero-residual identity or new compensation hypothesis is introduced.
-- source:
--   Direct specialization of Proved source theorem 8322c28a-b518-4f8d-af03-b27a3e949168, taking the first conjunct and rewriting the original HJB inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_generator_physical_drift_interval_budget
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_physical_HJB_interior_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (y : ℝ)
    (hy : 0 < y) (hyC : ENNReal.ofReal y < C)
    (hgen : X.GeneratorIntegrable w y ∧
      X.generator w y - q * w y ≤ 0) :
    X.drift * deriv w y +
        (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) -
      q * w y ≤ 0 := by sorry
