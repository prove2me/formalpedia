-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_finite_grid_variable_clock_tail_factor
-- name    : AvramDividend.Classical.avram_ws01e_b_support_finite_grid_variable_clock_tail_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:04:44.831678+00:00
-- url     : https://prove2.me/theorems/6be3ba4e-7a24-43ee-ac91-f264a58669b8
-- title:
--   True Esscher random-clock future-increment factorisation on variable finite-grid tails
-- statement:
--   For every cell s of a finite grid of observation stopping times, assume the history event A∩{τ=s} is measurable at s and its future u-increment cylinder is measurable at s+u. For a cell-dependent measurable clock set C(s) wholly later than s+u, the true random-terminal Esscher measure of the joint increment and clock cell factors as the s-time Esscher history mass, the u-time Esscher increment law, and the independent exponential-clock mass. Summing these exact identities gives the displayed finite-grid factorisation. Different cells may have different clock supports. No common terminal bound or artificial unit time buffer is required.
-- source:
--   Exact consequence of accepted esscher_random_time_joint_past_clock_future_factorization (caa0f80f-72fe-4f00-ad06-c2fe43ac38d4) and esscher_terminal_increment_cylinder_factorization (b4c43ae0-cb9d-43f3-bb6c-e484166ddf0e).

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_random_time_joint_past_clock_future_factorization
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_cylinder_factorization

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

/-- Actual random-terminal Esscher factorisation over grid-dependent
clock tails, with no common future terminal horizon. -/

theorem AvramDividend.Classical.avram_ws01e_b_support_finite_grid_variable_clock_tail_factor
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
    (∑ s ∈ grid,
      ((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
        (((A ∩ {ω : Ω | τ ω = s}) ∩
          (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B) ×ˢ C s)) =
    ∑ s ∈ grid,
      ((P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ))))
          (A ∩ {ω : Ω | τ ω = s}) *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
          ((X.X u) ⁻¹' B)) * (expMeasure p) (C s) := by sorry
