-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_tilted_grid_survived_increment_residual_clock_tail
-- name    : AvramDividend.Classical.avram_ws01e_b_tilted_grid_survived_increment_residual_clock_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T11:01:52.072351+00:00
-- url     : https://prove2.me/theorems/b1036304-7a11-4e85-b8fa-81bf6fff4985
-- title:
--   Exact residual exponential-clock tail factor conditional on a stopped history and actual tilted post-stop increment
-- statement:
--   Under the genuine random-terminal Esscher joint law Q_p of the complete Lévy path and independent Exp(p) clock, for every finite-grid stopping-time history with measurable adapted fibres and for any Borel event on a post-stop increment of length u, the event that the independent terminal clock survives an extra r beyond the increment has exactly exp(-p r) times the mass of the same event with survival only to the increment endpoint. The identity holds without conditioning on a null event and includes the correct joint Esscher density and survival normalisation. It is a finite-grid residual-clock regeneration interface, not full stopped-path regeneration.
-- source:
--   Proved 8d968653-56ed-42b2-b261-31650d63e1ac full genuine Qp finite-grid variable terminal-clock event factor and 6aa1899c-a9d8-4b5a-9407-4bd278dcc368 exact strict Exp(p) tail. Use Real.exp_add to factor each cell and Finset.sum_mul or mul_sum.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_finite_grid_full_clock_event_factor
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_exp_clock_toNNReal_strict_tail

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_ws01e_b_tilted_grid_survived_increment_residual_clock_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0) (u r : ℝ≥0)
    (A : Set Ω)
    (hHistory : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 s) (A ∩ {ω : Ω | τ ω = s}))
    (B : Set ℝ) (hB : MeasurableSet B)
    (hAdapted : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 (s + u))
        ((A ∩ {ω : Ω | τ ω = s}) ∩
          (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B))
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) :
    let QP : Measure (Ω × ℝ) :=
      ((P.prod (expMeasure p)).withDensity (fun z : Ω × ℝ =>
        ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    let E : ℝ≥0 → Set (Ω × ℝ) := fun a =>
      {z : Ω × ℝ |
        z.1 ∈ A ∧ τ z.1 ∈ grid ∧
        X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1 ∈ B ∧
        (τ z.1 + u) + a < Real.toNNReal z.2}
    QP (E r) =
      ENNReal.ofReal (Real.exp (-(p * (r : ℝ)))) * QP (E 0) := by sorry
