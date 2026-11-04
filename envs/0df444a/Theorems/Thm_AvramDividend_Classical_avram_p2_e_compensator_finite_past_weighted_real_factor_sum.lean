-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_past_weighted_real_factor_sum
-- name    : AvramDividend.Classical.avram_p2_e_compensator_finite_past_weighted_real_factor_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:01:04.159304+00:00
-- url     : https://prove2.me/theorems/8cefac71-d122-41b6-ba4f-205afbcf0637
-- title:
--   Finite original predictable-simple weighted count has exact real source mean with no Levy-rate assumption
-- statement:
--   For finite collections of actual original jump-count rectangles, each with a finite count mean and a nonnegative original Fs-measurable finite-mean past weight, the real signed-integral-compatible sum is integrable. Its expectation equals the sum of the independent-increment weighted products E[W_i] E[N_i], with no Levy ν-rate, Poisson replacement or compensator hypothesis.
-- source:
--   Proved P2-E rate-free real integrability 983cbffc and real factorisation b38c4b95, pinned Mathlib MeasureTheory.integrable_finset_sum and integral_finset_sum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_mean_past_weighted_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_mean_past_weighted_real_factor

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_e_compensator_finite_past_weighted_real_factor_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ≥0) (hst : ∀ i ∈ S, s i ≤ t i)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (W : ι → Ω → ℝ≥0∞)
    (hW : ∀ i ∈ S, Measurable[𝓕 (s i)] (W i))
    (hWfinite : ∀ i ∈ S, (∫⁻ ω, W i ω ∂P) < ⊤)
    (hNfinite : ∀ i ∈ S, (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (t i) ×ˢ B i) ∂P) < ⊤) :
    let J : ι → Ω → ℝ := fun i ω => (W i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (t i) ×ˢ B i)).toReal
    let rate : ι → ℝ := fun i =>
      ((∫⁻ ω, W i ω ∂P) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (t i) ×ˢ B i) ∂P)).toReal
    Integrable (fun ω => ∑ i ∈ S, J i ω) P ∧
      (∫ ω, ∑ i ∈ S, J i ω ∂P) = ∑ i ∈ S, rate i := by sorry
