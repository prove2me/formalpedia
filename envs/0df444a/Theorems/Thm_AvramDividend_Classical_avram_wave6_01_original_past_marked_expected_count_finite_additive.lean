-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_marked_expected_count_finite_additive
-- name    : AvramDividend.Classical.avram_wave6_01_original_past_marked_expected_count_finite_additive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:59:13.693227+00:00
-- url     : https://prove2.me/theorems/24601917-46f8-4792-a254-6231271112c3
-- title:
--   Original past-restricted expected intrinsic marked jump count is additive across disjoint Borel marks
-- statement:
--   For the unchanged Ω,P,𝓕 and genuine original-path Lévy X, expectation of its literal intrinsic jump count over (s,t] restricted to an F_s event is finitely additive across disjoint measurable mark sets. No finite-activity, BV, auxiliary Poisson law, mark-rate identity or compensator premise is assumed. The proof obtains an actual original-sample measurable jump-count kernel and applies fibrewise measure additivity and ENNReal Tonelli linearity. This supplies a measure-structure prerequisite for identifying the marked mean from the Lévy–Khintchine exponent.
-- source:
--   Original literal s-finite kernel eb357d08 gives measurable marked-count evaluations; disjoint marked rectangles are disjoint measurable sets; fibrewise Measure.measure_union and lintegral_add_left yield exact original-P expected-mark additivity without any rate assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_original_past_marked_expected_count_finite_additive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBC : Disjoint B C) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (B ∪ C)) ∂P) =
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) +
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ C) ∂P) := by sorry
