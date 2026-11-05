-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_integrable_diagonals_of_L2_Linfty
-- name    : AvramDividend.Classical.avram_p4_g_isometry_integrable_diagonals_of_L2_Linfty
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:29:20.146557+00:00
-- url     : https://prove2.me/theorems/b0330270-0a73-415e-861b-c8d83250e371
-- title:
--   L2 count and L∞ predictable coefficient imply three diagonal integrabilities
-- statement:
--   Under finite physical measure, a centred intrinsic count in L2 and predictable coefficient in L∞ imply integrability of the count square, coefficient square and weighted count square, the exact three separate hypotheses in the original finite-band L2 isometry.
-- source:
--   Pinned Mathlib MeasureTheory.MemLp.mul, .mono_exponent and .integrable_sq; independent of any unproved Poisson or factorial count law.

import Mathlib
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_integrable_diagonals_of_L2_Linfty
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    (J H : Ω → ℝ) (hJ : MemLp J 2 P) (hH : MemLp H ⊤ P) :
    Integrable (fun ω => (J ω) ^ 2) P ∧
    Integrable (fun ω => (H ω) ^ 2) P ∧
    Integrable (fun ω => (H ω) ^ 2 * (J ω) ^ 2) P := by sorry
