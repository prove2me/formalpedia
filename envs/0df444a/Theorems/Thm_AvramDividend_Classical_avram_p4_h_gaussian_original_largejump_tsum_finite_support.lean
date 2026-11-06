-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largejump_tsum_finite_support
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_largejump_tsum_finite_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:38:07.378342+00:00
-- url     : https://prove2.me/theorems/e45c2694-a4b4-4794-b13e-877dfcebff94
-- title:
--   Actual source large negative jumps form an exact finite sum on every bounded horizon
-- statement:
--   On the original sample path of X, all jump times with marks z<=-1 before T form a finite Finset. The signed large-jump series restricted to (0,T] equals exactly its finite sum, with no first moment or compensator assumptions. This is the source-exact pathwise Jlarge component needed to subtract large jumps from X.
-- source:
--   Proved P2-H original cadlag jump test tsum equals actual finite sum f027d528; specialise its test to f(z)=z if z<=-1 and 0 otherwise with near-zero cutoff delta=1.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_original_jump_test_tsum_eq_actual_finset
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_largejump_tsum_finite_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧ j u ≤ -1) ∧
      (∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ T then (if j u ≤ -1 then j u else 0) else 0) =
        ∑ u ∈ F, j u := by sorry
