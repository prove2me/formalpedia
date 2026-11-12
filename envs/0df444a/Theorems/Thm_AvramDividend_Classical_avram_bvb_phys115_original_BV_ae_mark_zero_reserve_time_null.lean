-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys115_original_BV_ae_mark_zero_reserve_time_null
-- name    : AvramDividend.Classical.avram_bvb_phys115_original_BV_ae_mark_zero_reserve_time_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:57:17.682973+00:00
-- url     : https://prove2.me/theorems/12d7bb7c-d9f7-44e2-a81d-9a1875b0ed84
-- title:
--   Almost every original BV jump mark has time-null ruin-contact fibre
-- statement:
--   Under the original Standing bounded-variation assumptions and for any measurable reserve path, for Levy-almost every jump mark z the set of times at which the reserve equals minus z is null. This is the Fubini and dominated-convergence ready form of the exact ruin-contact exceptional-set exclusion in the physical-grid quadrature phys95.
-- source:
--   Original BV phys95 markwise dominated convergence; Proved phys113 and Mathlib measure_eq_zero_iff_ae_notMem

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_phys115_original_BV_ae_mark_zero_reserve_time_null {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing) (hBV : X.BoundedVariation) (μ : Measure ℝ≥0) [SFinite μ] (U : ℝ≥0 → ℝ) (hU : Measurable U) : ∀ᵐ z ∂X.ν, μ {t : ℝ≥0 | U t = -z} = 0 := by sorry
