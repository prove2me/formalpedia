-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_centered_count_L2_of_factorial_integrability
-- name    : AvramDividend.Classical.avram_p4_g_isometry_centered_count_L2_of_factorial_integrability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:34:39.685201+00:00
-- url     : https://prove2.me/theorems/a6c1c8ca-6d42-48b0-9864-f25d097b6b88
-- title:
--   Centred intrinsic finite-band count L2 from factorial integrability
-- statement:
--   For an original real-valued intrinsic jump count J under a finite physical measure, integrability of J and of its second factorial count imply J−r ∈L2. It removes a distinct integrability requirement from the finite-grid isometry once the actual first and factorial count moments are supplied.
-- source:
--   Pure Mathlib algebraic factorial identity, Integrable.add, memLp_two_iff_integrable_sq; source count identification remains in caller.

import Mathlib
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_centered_count_L2_of_factorial_integrability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    (J : Ω → ℝ) (r : ℝ)
    (hJ : Integrable J P)
    (hFactorial : Integrable (fun ω => J ω * (J ω - 1)) P) :
    MemLp (fun ω => J ω - r) 2 P := by sorry
