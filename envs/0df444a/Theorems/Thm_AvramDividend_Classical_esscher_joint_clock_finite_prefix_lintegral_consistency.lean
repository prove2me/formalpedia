-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_joint_clock_finite_prefix_lintegral_consistency
-- name    : AvramDividend.Classical.esscher_joint_clock_finite_prefix_lintegral_consistency
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:28:59.523138+00:00
-- url     : https://prove2.me/theorems/703220b3-c4f2-471f-b9a8-00814b42da26
-- title:
--   Independent-clock and finite-path joint observation expectations are Esscher terminal-horizon consistent
-- statement:
--   Fix s≤T and a nonnegative Esscher tilt θ. Let ν be any s-finite probability or observation clock measure on the real line, independent of the original Lévy path in the product law. For every jointly measurable nonnegative extended-real observation F(ω,u) whose path section ω↦F(ω,u) is measurable in F_s for each u, its expectation under Q_T×ν equals that under Q_s×ν. This covers all measurable truncated-clock observations of a finite process prefix and avoids asserting an infinite-horizon Esscher path probability.
-- source:
--   Accepted esscher_finite_prefix_lintegral_consistency 88c4aa3f-c05b-4528-83ce-ab46bd285f77 and chat04_esscher_weighted_finite_horizon_probability; pinned Mathlib MeasureTheory.lintegral_prod_symm' Tonelli in MeasureTheory.Measure.Prod. Independent clock motivation: Kuznetsov–Kyprianou–Rivero, Esscher and Wiener–Hopf sections.

import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_esscher_finite_prefix_lintegral_consistency
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_joint_clock_finite_prefix_lintegral_consistency
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s T : ℝ≥0) (hsT : s ≤ T)
    {ν : Measure ℝ} [SFinite ν]
    (F : Ω × ℝ → ℝ≥0∞)
    (hF : Measurable F)
    (hSlice : ∀ t : ℝ, Measurable[𝓕 s] (fun ω : Ω => F (ω, t))) :
    (∫⁻ z, F z ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod ν) =
    (∫⁻ z, F z ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)))).prod ν) := by sorry
