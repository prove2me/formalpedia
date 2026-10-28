-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_finite_grid_full_clock_event_factor
-- name    : AvramDividend.Classical.avram_ws01e_b_support_finite_grid_full_clock_event_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:19:39.96866+00:00
-- url     : https://prove2.me/theorems/8d968653-56ed-42b2-b261-31650d63e1ac
-- title:
--   True exponential-clock Esscher full finite-grid stopped-increment event factorisation
-- statement:
--   The true observation-clock Esscher weighted probability of a full stopped-increment event, with finite-valued stopping time and cell-dependent allowed observation-clock times, equals the finite sum over stopping cells of the s-tilted history mass times the u-tilted increment law times exponential clock mass. Unlike a cylinder-sum identity, the left hand side is the probability of one natural random-clock event. The statement derives individual product-cell measurability from adapted history at s+u and measurable clock cells, retaining explicit clock-support assumptions, and avoids any unproved Wiener–Hopf independence.
-- source:
--   Directly uses Proved variable-clock Esscher factorisation 6be3ba4e-7a24-43ee-ac91-f264a58669b8, with a short inlined disjoint-grid measure decomposition and filtration-derived cell measurability.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_finite_grid_variable_clock_tail_factor

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
/-- Genuine Esscher random-clock law for the complete finite-grid
stopped-increment and variable-tail event, not just its cell sum. -/

theorem AvramDividend.Classical.avram_ws01e_b_support_finite_grid_full_clock_event_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0) (u : ℝ≥0)
    (A : Set Ω)
    (hHistory : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 s) (A ∩ {ω : Ω | τ ω = s}))
    (B : Set ℝ) (hB : MeasurableSet B)
    (hAdapted : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 (s + u))
        ((A ∩ {ω : Ω | τ ω = s}) ∩
          (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B))
    (C : ℝ≥0 → Set ℝ)
    (hC : ∀ s ∈ grid, MeasurableSet (C s))
    (hClockTail : ∀ s ∈ grid, ∀ t ∈ C s,
      s + u ≤ Real.toNNReal t)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) :
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
      {z : Ω × ℝ |
        z.1 ∈ A ∧ τ z.1 ∈ grid ∧
        X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1 ∈ B ∧
        z.2 ∈ C (τ z.1)} =
    ∑ s ∈ grid,
      ((P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ))))
          (A ∩ {ω : Ω | τ ω = s}) *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
          ((X.X u) ⁻¹' B)) * (expMeasure p) (C s) := by sorry
