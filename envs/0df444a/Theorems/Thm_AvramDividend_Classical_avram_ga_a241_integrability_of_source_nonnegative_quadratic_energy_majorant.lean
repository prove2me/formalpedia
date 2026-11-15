-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a241_integrability_of_source_nonnegative_quadratic_energy_majorant
-- name    : AvramDividend.Classical.avram_ga_a241_integrability_of_source_nonnegative_quadratic_energy_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:10:58.716778+00:00
-- url     : https://prove2.me/theorems/6e7f28dd-6bb9-46c5-882f-734cc5717764
-- title:
--   Measurable nonnegative Gaussian full-grid quadratic source integrable under integrable centred energy majorant
-- statement:
--   If the nonnegative source full-cell quadratic energy F is a.e. strongly measurable and bounded by twice the nonnegative integrable centered prefix Gaussian energy E plus twice a nonnegative finite deterministic drift-square mass a, then every F_m is integrable. This generic exact positive energy majorant permits original source Gaussian a170 plus a195 to establish actual full-cell raw squared-increment integrability, closing the premise in a240.
-- source:
--   True original Gaussian source energy majorant a195 and a170, generic integrability domination

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a241_integrability_of_source_nonnegative_quadratic_energy_majorant
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F E : ℕ → Ω → ℝ) (a : ℕ → ℝ)
    (ha : ∀ m, 0 ≤ a m)
    (hFm : ∀ m, AEStronglyMeasurable (F m) P)
    (hEI : ∀ m, Integrable (E m) P)
    (hFpos : ∀ m ω, 0 ≤ F m ω)
    (hEpos : ∀ m ω, 0 ≤ E m ω)
    (hPt : ∀ m ω, F m ω ≤ 2 * E m ω + 2 * a m) :
    ∀ m, Integrable (F m) P := by sorry
