-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a174_measurable_gaussian_quadratic_cross_integrable_of_centered_energy
-- name    : AvramDividend.Classical.avram_ga_a174_measurable_gaussian_quadratic_cross_integrable_of_centered_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:50:39.638059+00:00
-- url     : https://prove2.me/theorems/1a4b0c65-01ee-4331-9ee7-f747d108bf66
-- title:
--   Gaussian finite stopped-mask quadratic raw-centred cross integrability from centred source square energy
-- statement:
--   For any measurable finite mask on a probability space and measurable real Gaussian source increments Z, integrability of the masked sum of squared centred increments ensures integrability of the masked sum of absolute differences of raw and centred squares at any fixed drift displacement d. Uses exact Young inequality and triangular cross bound already Proved as ga_a84/ga_a85.
-- source:
--   Proved ga_a84 and ga_a85, measurable finite masks, integrable square energy and finite measure constant.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a85_gaussian_raw_centered_square_triangle
import Theorems.Thm_AvramDividend_Classical_avram_ga_a84_centered_gaussian_quadratic_cross_young_product
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a174_measurable_gaussian_quadratic_cross_integrable_of_centered_energy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (S : Finset ℕ) (A : ℕ → Ω → Prop)
    [∀ i, DecidablePred (A i)]
    (hA : ∀ i, MeasurableSet {ω | A i ω})
    (Z : ℕ → Ω → ℝ) (hZ : ∀ i, Measurable (Z i))
    (d : ℝ)
    (hEI : Integrable (fun ω =>
      ∑ i ∈ S, if A i ω then (Z i ω)^2 else 0) P) :
    Integrable (fun ω =>
      ∑ i ∈ S, if A i ω then
        |(Z i ω + d)^2 - (Z i ω)^2| else 0) P := by sorry
