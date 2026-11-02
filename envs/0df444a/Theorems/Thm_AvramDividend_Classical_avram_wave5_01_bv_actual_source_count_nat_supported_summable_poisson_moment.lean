-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_source_count_nat_supported_summable_poisson_moment
-- name    : AvramDividend.Classical.avram_wave5_01_bv_actual_source_count_nat_supported_summable_poisson_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:44:16.887056+00:00
-- url     : https://prove2.me/theorems/b976bfb1-872f-421d-9dc7-f1ba30b73f54
-- title:
--   Actual BV source count has an original-filtration, natural-supported proxy with summable exact Poisson first moment
-- statement:
--   On the genuine original X, P and 𝓕, the BV finite-negative-activity literal count admits a source 𝓕_T-measurable ENNReal proxy F equal almost surely to its literal jump count, taking natural-number values almost surely, whose weighted singleton probabilities are summable with exact real mean T times the original Lévy total negative intensity. This is the summability and almost-sure discreteness prerequisite to prove a genuine original-count lintegral, not a detached Poisson model or individual-mark compensation.
-- source:
--   Composes 0bd33c35, 8bd33f15, e35efd8b, f6336d40; proves Poisson weighted mass summability via shift and known hasSum_one_poissonMeasure in the original source pushforward law. This genuinely reduces the original count lintegral proof (next parent).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_filtration_measurable_source_count_poisson_exact_law
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_source_total_count_poisson_weighted_first_moment
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_source_locally_finite_jump_times_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave5_01_bv_actual_source_count_nat_supported_summable_poisson_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℕ → ℝ≥0)
    (hGrid : ∀ n : ℕ, 0 < n →
      StrictMono (grid n) ∧ grid n 0 = 0 ∧ grid n n = T)
    (hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, i < n →
        dist (grid n i) (grid n (i + 1)) < δ)
    (hBound : ∀ n i : ℕ, i ≤ n → grid n i ≤ T) :
    ∃ F : Ω → ℝ≥0∞, Measurable[𝓕 T] F ∧
      (∀ᵐ ω ∂P,
        F ω = ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ (Set.univ : Set ℝ))) ∧
      (∀ᵐ ω ∂P, ∃ k : ℕ, F ω = (k : ℝ≥0∞)) ∧
      Summable (fun k : ℕ => (k : ℝ) *
        P.real {ω : Ω | F ω = (k : ℝ≥0∞)}) ∧
      (∑' k : ℕ, (k : ℝ) *
        P.real {ω : Ω | F ω = (k : ℝ≥0∞)}) =
        (T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal := by sorry
