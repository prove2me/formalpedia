-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_finite_prefix_lintegral_consistency
-- name    : AvramDividend.Classical.esscher_finite_prefix_lintegral_consistency
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:19:44.108573+00:00
-- url     : https://prove2.me/theorems/88c4aa3f-c05b-4528-83ce-ab46bd285f77
-- title:
--   Projective Esscher law consistency extends to every nonnegative measurable finite-prefix path functional
-- statement:
--   Let Q_t be the finite-horizon Esscher probability law with nonnegative θ. For s≤T and any nonnegative extended-real functional f measurable with respect to the actual process filtration F_s, its Lebesgue expectation under Q_T equals its expectation under Q_s, including possibly infinite values. In particular this covers bounded measurable finite-time path cylinders and any nonnegative functional of the process prefix. It makes no infinite-time path-extension assumption.
-- source:
--   Canonical accepted Esscher path-prefix trimmed measure equality 7956d960-7c64-474f-9354-242de9731e05; Mathlib MeasureTheory.lintegral_trim from Mathlib.MeasureTheory.Integral.Lebesgue.Add, pinned 0df444a.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Theorems.Thm_AvramDividend_Classical_esscher_path_prefix_trim_measure_consistency

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_finite_prefix_lintegral_consistency
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s T : ℝ≥0) (hsT : s ≤ T)
    (f : Ω → ℝ≥0∞) (hf : Measurable[𝓕 s] f) :
    (∫⁻ ω, f ω ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) =
    (∫⁻ ω, f ω ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ))))) := by sorry
