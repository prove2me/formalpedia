-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_cutoff_sup_eq_total_of_coverage
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_jump_cutoff_sup_eq_total_of_coverage
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:44:20.007062+00:00
-- url     : https://prove2.me/theorems/06e7283b-65d7-4a41-bcf7-89ce26d1cbbd
-- title:
--   Actual original negative-jump cutoff totals converge to the full intrinsic source left-jump mass
-- statement:
--   For the original spectrally negative Levy process and a fixed source sample path, if a decreasing sequence of ENNReal magnitude thresholds eventually falls below each strictly positive left-jump magnitude in (0,T], then the supremum of the corresponding genuine source cutoff sums equals the entire actual jump total. No compensator, rate, integrability, BV or auxiliary process representation is assumed.
-- source:
--   Apply avram_p3_a_bvdrift_cutoff_tsum_monotone_convergence_core to the genuine source left-jump magnitude masked by (0,T]; threshold coverage on positive original marks implies generic pointwise coverage.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_cutoff_tsum_monotone_convergence_core

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Actual original negative-jump cutoff totals increase to their full source
jump mass if thresholds decrease and eventually include each positive jump. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_jump_cutoff_sup_eq_total_of_coverage
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (ω : Ω)
    (ε : ℕ → ℝ≥0∞) (hε : Antitone ε)
    (hCover : ∀ v : ℝ≥0, 0 < v → v ≤ T →
      0 < ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) →
      ∃ n : ℕ, ε n < ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)) :
    let M : ℝ≥0 → ℝ≥0∞ := fun v : ℝ≥0 => if 0 < v ∧ v ≤ T then ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) else 0
    (⨆ n : ℕ, ∑' v : ℝ≥0, if ε n < M v then M v else 0) =
      ∑' v : ℝ≥0, M v := by sorry
