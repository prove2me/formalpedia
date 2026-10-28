-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_tilted_grid_survived_history_two_increment_joint_map_law
-- name    : AvramDividend.Classical.avram_ws01e_b_tilted_grid_survived_history_two_increment_joint_map_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:57:11.39975+00:00
-- url     : https://prove2.me/theorems/d5b50df8-bf18-4abf-9379-c806e0bb1b7f
-- title:
--   Joint Borel pushforward law for two genuine tilted post-stop increments on survived finite-grid histories
-- statement:
--   For the actual random-terminal Esscher joint path and independent exponential clock law, and finite-grid stopped history E whose clock-support cells lie after both successive post-stop increments, the unnormalised joint pushforward measure of the two actual consecutive future increments equals the exact survival mass QP(E) times the product of the two genuine tilted deterministic-time increment marginal laws. This is an equality on every Borel subset of R×R, extending the accepted two-step rectangle factor, and retains the real exponential-clock density. Requires explicit filtration-adapted cylinder sections and measurable maps; no full stopped path independence or WH factor is assumed.
-- source:
--   Derive via pinned Measure.ext_prod, Measure.map_apply, Measure.restrict_apply, Measure.prod_prod and canonically Proved two-step actual random-terminal survived-history factor 61afe72c, with QP probability from 146b0027 and finite-terminal tilted QV normalisation 6c6f7684.

import Mathlib
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_two_step_grid_survival_history_independence
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_ws01e_b_tilted_grid_survived_history_two_increment_joint_map_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0) (u v : ℝ≥0)
    (A : Set Ω)
    (hHistory : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 s) (A ∩ {ω : Ω | τ ω = s}))
    (hBaseMiddle : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 (s + u)) (A ∩ {ω : Ω | τ ω = s}))
    (hBaseFinal : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 ((s + u) + v)) (A ∩ {ω : Ω | τ ω = s}))
    (hMiddle : ∀ (B₁ : Set ℝ), MeasurableSet B₁ → ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 (s + u))
        ((A ∩ {ω : Ω | τ ω = s}) ∩
          (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B₁))
    (hFinal : ∀ (B₁ B₂ : Set ℝ), MeasurableSet B₁ → MeasurableSet B₂ →
      ∀ s ∈ grid, @MeasurableSet Ω (𝓕 ((s + u) + v))
        (((A ∩ {ω : Ω | τ ω = s}) ∩
          (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B₁) ∩
          (fun ω : Ω => X.X ((s + u) + v) ω -
            X.X (s + u) ω) ⁻¹' B₂))
    (C : ℝ≥0 → Set ℝ)
    (hC : ∀ s ∈ grid, MeasurableSet (C s))
    (hClockTail : ∀ s ∈ grid, ∀ t ∈ C s,
      (s + u) + v ≤ Real.toNNReal t)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (hY : Measurable (fun z : Ω × ℝ =>
      (X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1,
       X.X ((τ z.1 + u) + v) z.1 - X.X (τ z.1 + u) z.1)))
    (hXu : Measurable (X.X u)) (hXv : Measurable (X.X v)) :
    let QP : Measure (Ω × ℝ) :=
      ((P.prod (expMeasure p)).withDensity (fun z : Ω × ℝ =>
        ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    let QU : Measure Ω :=
      P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))
    let QV : Measure Ω :=
      P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X v ω - (v : ℝ) * X.ψ θ)))
    let E : Set (Ω × ℝ) :=
      {z : Ω × ℝ | z.1 ∈ A ∧ τ z.1 ∈ grid ∧ z.2 ∈ C (τ z.1)}
    Measure.map (fun z : Ω × ℝ =>
      (X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1,
       X.X ((τ z.1 + u) + v) z.1 - X.X (τ z.1 + u) z.1))
      (QP.restrict E) =
    QP E • ((Measure.map (X.X u) QU).prod (Measure.map (X.X v) QV)) := by sorry
