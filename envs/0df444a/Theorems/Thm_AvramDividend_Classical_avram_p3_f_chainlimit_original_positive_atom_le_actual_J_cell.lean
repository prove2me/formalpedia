-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_positive_atom_le_actual_J_cell
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_positive_atom_le_actual_J_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:21:30.274145+00:00
-- url     : https://prove2.me/theorems/b59097be-c75c-49c8-bce5-1800ba00678d
-- title:
--   Each true positive-time original negative jump is bounded by its physical J cell mass
-- statement:
--   Almost surely for every original bounded-variation Lévy path and any physical cell (s,t] containing a genuine positive-time negative source jump at v, its actual magnitude leftLim X.X(v)-X.X(v) is at most the original full negative-jump accumulation J(t)-J(s). This is derived from exact original BV summability, source interval additivity, pathwise absence of positive jumps, and nonnegative real tsum comparison. It provides the source-exact atom-capture inequality needed to bound the unmarked C1 mesh tail without changing X or assuming generator compensation.
-- source:
--   Proved original raw interval absolute convergence f0ec726b, cumulative source interval additivity 50ef916b, and true positive-time left-jump nonnegative 561ccef5; singleton support comparison via Summable.tsum_le_tsum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_disjoint_interval_additivity
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_positive_atom_le_actual_J_cell
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' z : ℝ≥0, if 0 < z ∧ z ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) z - X.X z ω
        else 0
      ∀ s t v : ℝ≥0, s < v → v ≤ t →
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω ≤
          J t - J s := by sorry
