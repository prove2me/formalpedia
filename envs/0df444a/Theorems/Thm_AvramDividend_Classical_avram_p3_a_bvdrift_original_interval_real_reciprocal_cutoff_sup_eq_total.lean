-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_real_reciprocal_cutoff_sup_eq_total
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_interval_real_reciprocal_cutoff_sup_eq_total
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:32:49.506583+00:00
-- url     : https://prove2.me/theorems/955259d9-9616-4ccc-b457-0e210a88e74f
-- title:
--   Actual original BV source negative-jump total is the real reciprocal-cutoff supremum on every interval
-- statement:
--   For the original bounded-variation spectrally negative Levy process and its original sample law, almost surely and simultaneously for every ordered interval (s,t], the real-valued total of all actual negative left jumps equals the supremum of real-valued totals of jumps exceeding reciprocal size cutoffs. No compensator, Poisson realisation, extra process representation or fixed time horizon is assumed.
-- source:
--   Specialise the accepted all-interval original BV finite total theorem e80cd41a and new finite-toreal generic reciprocal cutoff theorem (pending acceptance) to the genuine original left-jump magnitude assignment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_finite_reciprocal_cutoff_tsum_toReal_iSup

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The genuine bounded-variation source left-jump magnitude series is the
supremum of real-valued reciprocal cutoff totals on every ordered interval. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_interval_real_reciprocal_cutoff_sup_eq_total
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      let M : ℝ≥0 → ℝ≥0∞ := fun v : ℝ≥0 =>
        if s < v ∧ v ≤ t then
          ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0
      (⨆ n : ℕ, (∑' v : ℝ≥0,
        if (n : ℝ≥0∞)⁻¹ < M v then M v else 0).toReal) =
        (∑' v : ℝ≥0, M v).toReal := by sorry
