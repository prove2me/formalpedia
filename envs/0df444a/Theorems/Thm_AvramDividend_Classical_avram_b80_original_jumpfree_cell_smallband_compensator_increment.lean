-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b80_original_jumpfree_cell_smallband_compensator_increment
-- name    : AvramDividend.Classical.avram_b80_original_jumpfree_cell_smallband_compensator_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:25:44.744622+00:00
-- url     : https://prove2.me/theorems/1d2fec3a-f5e0-4022-acce-6f540a54ffa5
-- title:
--   Original finite small-negative-band compensated source increment is drift-only on true jumpfree intervals
-- statement:
--   The original finite-band compensated negative-jump process is exactly the finite sum of the corresponding physical source jump marks up to time t minus the original Lévy intensity moment multiplied by t, by Proved avram_p4_h_gaussian_original_compensated_smallband_eq_finite_jump_sum. At two actual source times s<=t with no original X negative-jump mark on (s,t], those finite sets coincide: a newly counted negative mark would contradict the no-jump assumption. Subtract the exact compensation representations to show its signed increment equals the deterministic negative Lévy small-band first-moment compensator times the elapsed physical time. This is the intrinsic source-exact no-jump precursor to B78's hSmall and avoids an unrelated process or a global negative-mark second moment. It neither requires s,t to be deterministic, nor assumes post-ruin evaluation.
-- source:
--   Proved original raw signed smallband integral equals actual finite marked source jump sum, UUID 158e793f-6e18-4374-932e-8e1bf5e8fd2a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smallband_signed_integral_eq_finite_jump_sum
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The exact original compensated small negative band has only its compensator drift on a genuine no-jump interval. -/

theorem AvramDividend.Classical.avram_b80_original_jumpfree_cell_smallband_compensator_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (s t : ℝ≥0) (hst : s ≤ t) (ω : Ω)
    (hNoJump : ∀ u : ℝ≥0, s < u → u ≤ t →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω =
      -((t : ℝ) - (s : ℝ)) *
        (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν) := by sorry
