-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_source_jump_times_finite_of_finite_range
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_source_jump_times_finite_of_finite_range
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:36:15.871584+00:00
-- url     : https://prove2.me/theorems/a4db3295-36e6-4747-988b-9872882494e1
-- title:
--   Original BV Lévy process has finitely many genuine nonzero source jumps on a horizon when its actual residual range is finite
-- statement:
--   For the actual original BV spectrally negative Lévy process on its same Ω and P, if its drift residual is known to have finite range on [0,T] almost surely, then the genuine original X has only finitely many nonzero jumps in (0,T] on a P-full event. This refers exactly to the source marked counting measure's positive-time jump support, with no equal-law Poisson replacement. It combines a canonically Proved strict residual-jump finiteness provider with the canonically Proved exact original source-mark ↔ residual jump equivalence.
-- source:
--   Canonical Proved dad57e67-afa6-4bc6-82ab-2ad39a1faa29 provides finite strict residual-jump times under finite-range source hypothesis. Exact source nonzero X-jump iff strict drift-residual jump theorem 7423dfee-c973-497f-a274-07e572cbd7a0 is canonically Proved. The real original-X jump-time set is a subset of the Proved finite residual-jump set.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_strict_residual_jump_times_finite_of_finite_range
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_source_nonzero_jump_iff_strict_drift_residual_jump

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_source_jump_times_finite_of_finite_range
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (T : ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∃ S : Finset ℝ,
      ∀ t : ℝ≥0, t ≤ T →
        (t : ℝ) * X.drift - X.X t ω ∈ S) :
    ∀ᵐ ω ∂P,
      {t : ℝ≥0 |
        t ≤ T ∧ 0 < t ∧
          X.X t ω -
            Function.leftLim (fun u : ℝ≥0 => X.X u ω) t ≠ 0}.Finite := by sorry
