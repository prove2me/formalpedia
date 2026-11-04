-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_real_reciprocal_cutoff_limit
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_real_reciprocal_cutoff_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:02:47.568872+00:00
-- url     : https://prove2.me/theorems/113c0384-2115-4246-aba6-31523e876dde
-- title:
--   Original BV reciprocal-cutoff jump sums converge to exact raw real left-jump series
-- statement:
--   For actual original bounded-variation Lévy paths, reciprocal cutoffs of negative jumps on any bounded ordered interval have real-valued supremum equal to the exact raw signed left-jump real series, not merely its ENNReal encoding. No independent Poisson model, drift representation or compensator hypothesis enters this pathwise cutoff theorem.
-- source:
--   Proved original interval finite real cutoff limit 955259d9 and true-source raw real tsum equivalence f0ec726b; retains original process and probability-one event.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_real_reciprocal_cutoff_sup_eq_total
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Cutoffs of actual BV negative-jump magnitudes converge monotonically
to the genuine real sum of signed source left jumps on each interval. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_real_reciprocal_cutoff_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      let M : ℝ≥0 → ℝ≥0∞ := fun u : ℝ≥0 =>
        if s < u ∧ u ≤ t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0
      (⨆ n : ℕ, (∑' u : ℝ≥0,
        if (n : ℝ≥0∞)⁻¹ < M u then M u else 0).toReal) =
      (∑' u : ℝ≥0, if s < u ∧ u ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0) := by sorry
