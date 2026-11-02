-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_marked_expected_count_countably_additive
-- name    : AvramDividend.Classical.avram_wave6_01_original_past_marked_expected_count_countably_additive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:53:09.429484+00:00
-- url     : https://prove2.me/theorems/a2bad23f-6edb-41a8-8b55-4bd615c2108a
-- title:
--   Actual past-restricted original Lévy marked expected jump counts are sigma-additive
-- statement:
--   For unchanged Ω,P,𝓕,X, any past event A∈𝓕_s, and any pairwise disjoint sequence B_n of measurable real jump-mark sets, the expectation of the literal intrinsic jump count in (s,t] on ⋃B_n equals the infinite sum of the past-restricted expected original jump counts on each B_n. This is genuine countable additivity of the source-mark mean set function, without BV, Poisson-copy model, assumed compensator or identification with X.ν(B). It follows from the canonically Proved source s-finite measurable kernel, fibrewise measure_iUnion and ENNReal lintegral_tsum. Disjointness is expressed as an explicit Pairwise lambda.
-- source:
--   Proved source intrinsic s-finite kernel eb357d08 on the actual Ω and same X.X jump graph; use disjoint measure_iUnion at each original sample and lintegral_tsum after proving every marked rectangle count measurable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_original_past_marked_expected_count_countably_additive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hDisj : Pairwise (fun i j => Disjoint (B i) (B j))) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ (⋃ n, B n)) ∂P) =
    ∑' n, (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B n) ∂P) := by sorry
