-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_tilted_grid_survived_history_future_increment_map_law
-- name    : AvramDividend.Classical.avram_ws01e_b_tilted_grid_survived_history_future_increment_map_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:41:45.292987+00:00
-- url     : https://prove2.me/theorems/622f791e-6549-48ca-bab2-0bda06cebe01
-- title:
--   Full pushforward law of genuine tilted future increments on finite-grid survived histories
-- statement:
--   For a spectrally negative Lévy X with authentic joint random-terminal Esscher law Qp on path × independent Exp(p) clock, finite-grid stopped age τ and adapted history A, the unnormalised pushforward of Qp restricted to A∩{τ∈grid}∩{clock∈C(τ)} by the true post-stopped increment X_(τ+u)−X_τ equals the restricted event mass Qp(E) times the full genuine deterministic-time u Esscher increment law. This is a measure equality for all Borel tests, stronger as an interface than a single cylinder identity, with explicit joint, stopped-event, and increment measurability assumptions. It is suitable for measure-limits of capped stopping times; it does not yet establish full residual-clock/entire-path regeneration.
-- source:
--   Direct measure-ext and map/restrict/smul conversion of canonically Proved d5920281 finite-grid true random-terminal tilted survived-history increment factor, using source-verified 9032b4a2 map-law methodology under Q_T as a structural precedent.

import Mathlib
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_tilted_grid_stopped_increment_independent_of_survival_history

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_ws01e_b_tilted_grid_survived_history_future_increment_map_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0) (u : ℝ≥0)
    (A : Set Ω)
    (hHistory : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 s) (A ∩ {ω : Ω | τ ω = s}))
    (hBaseAdapted : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 (s + u))
        (A ∩ {ω : Ω | τ ω = s}))
    (hAdapted : ∀ B : Set ℝ, MeasurableSet B → ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 (s + u))
        ((A ∩ {ω : Ω | τ ω = s}) ∩
          (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B))
    (C : ℝ≥0 → Set ℝ)
    (hC : ∀ s ∈ grid, MeasurableSet (C s))
    (hClockTail : ∀ s ∈ grid, ∀ t ∈ C s,
      s + u ≤ Real.toNNReal t)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (hY : Measurable (fun z : Ω × ℝ =>
      X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1))
    (hXu : Measurable (X.X u)) :
    let QP : Measure (Ω × ℝ) :=
      ((P.prod (expMeasure p)).withDensity (fun z : Ω × ℝ =>
        ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    let QU : Measure Ω :=
      P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))
    let E : Set (Ω × ℝ) :=
      {z : Ω × ℝ | z.1 ∈ A ∧ τ z.1 ∈ grid ∧ z.2 ∈ C (τ z.1)}
    Measure.map (fun z : Ω × ℝ =>
      X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1)
      (QP.restrict E) = QP E • Measure.map (X.X u) QU := by sorry
