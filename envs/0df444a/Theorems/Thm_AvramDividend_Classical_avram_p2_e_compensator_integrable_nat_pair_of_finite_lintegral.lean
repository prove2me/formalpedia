-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_integrable_nat_pair_of_finite_lintegral
-- name    : AvramDividend.Classical.avram_p2_e_compensator_integrable_nat_pair_of_finite_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:08:07.260563+00:00
-- url     : https://prove2.me/theorems/f9f7ae3d-4c0e-480d-b318-88bff2a8bd96
-- title:
--   Finite measurable original chronological Nat pair mean implies its real integrability
-- statement:
--   A measurable nonnegative integer-valued pair count whose extended-real Lebesgue integral is finite has an integrable real cast. This provides the exact integrability step for the original chronological second factorial moment.
-- source:
--   Pinned ENNReal.measurable_toReal and hasFiniteIntegral_iff_ofReal, with the exact source original chronological Nat pair count after established measurability and Fatou finiteness.

import Mathlib

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_integrable_nat_pair_of_finite_lintegral
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (K : Ω → ℕ)
    (hMeas : Measurable (fun ω => (K ω : ℝ≥0∞)))
    (hFinite : (∫⁻ ω, (K ω : ℝ≥0∞) ∂μ) < ⊤) :
    MeasureTheory.Integrable (fun ω => (K ω : ℝ)) μ := by sorry
