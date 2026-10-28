-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_path_prefix_trim_measure_consistency
-- name    : AvramDividend.Classical.esscher_path_prefix_trim_measure_consistency
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T15:52:56.707186+00:00
-- url     : https://prove2.me/theorems/7956d960-7c64-474f-9354-242de9731e05
-- title:
--   Consistent Esscher densities induce one equal measure on every earlier path-filtration prefix
-- statement:
--   Let Q_t denote the true Esscher probability law at deterministic time t. For every s≤T, the measures Q_T and Q_s restricted via Mathlib Measure.trim to the sub-σ-algebra F_s are exactly equal as measures, rather than merely agreeing on one named event. This expresses a coherent finite-prefix path law independent of the terminal time chosen. It does not assert existence of a single infinite-horizon extension on the original Ω.
-- source:
--   Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions, Esscher finite-time path law §2.1; accepted Prove2Me chat04_esscher_finite_horizon_laws_consistent_on_past_events a74b3334-5c28-44d1-ae88-3057d26957f4; pinned Mathlib Measure.trim and trim_measurableSet_eq at 0df444a.

import Mathlib.MeasureTheory.Measure.Trim
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_path_prefix_trim_measure_consistency
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s T : ℝ≥0) (hsT : s ≤ T) :
    @Measure.trim Ω (𝓕 s) mΩ
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      (𝓕.le s) =
    @Measure.trim Ω (𝓕 s) mΩ
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ))))
      (𝓕.le s) := by sorry
