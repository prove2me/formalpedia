-- Prove2me | solution 1 for stochIter_measurable
-- status  : ACCEPTED   (disprove)
-- author  : @garyholm
-- created : 2026-11-16T09:44:49.404055+00:00
-- url     : https://prove2.me/submissions/cd70223b-3c02-4f0c-9d95-47af5987bf6b

import Mathlib
import Definitions.Def_ShorNonsmooth_Stochastic_StochasticSubgradientMethod
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
open MeasureTheory Filter Topology
open scoped InnerProductSpace
open ShorNonsmooth.Stochastic

theorem solution : ¬ (∀ {n : ℕ} {Ω : Type} {m0 : MeasurableSpace Ω}
    (ℱ : Filtration ℕ m0) (h : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hh_meas : ∀ j, Measurable (h j))
    (G : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (x₀ : EuclideanSpace ℝ (Fin n)) (j : ℕ),
    Measurable[(ℱ j : MeasurableSpace Ω)] (stochIter h G x₀ j)) := by
  intro H
  let ℱ : Filtration ℕ (⊥ : MeasurableSpace Bool) :=
    ⟨fun _ => ⊥, fun _ _ _ => le_rfl, fun _ => le_rfl⟩
  let e : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
  have he : e ≠ 0 := by
    intro h0
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) h0
    simp [e] at this
  let G : ℕ → Bool → EuclideanSpace ℝ (Fin 1) := fun _ ω => if ω then e else 0
  have hm := H ℱ (fun _ _ => (1 : ℝ)) (fun _ => measurable_const) G 0 1
  have hS : MeasurableSet[(⊥ : MeasurableSpace Bool)]
      (stochIter (fun _ _ => (1 : ℝ)) G 0 1 ⁻¹' {0}) := hm (measurableSet_singleton 0)
  have hpre : stochIter (fun _ _ => (1 : ℝ)) G 0 1 ⁻¹' {0} = {false} := by
    ext ω
    cases ω <;> simp [stochIter, G, he]
  rw [hpre] at hS
  rcases MeasurableSpace.measurableSet_bot_iff.1 hS with h1 | h1
  · have : false ∈ ({false} : Set Bool) := rfl
    rw [h1] at this
    exact this
  · have : true ∈ ({false} : Set Bool) := by rw [h1]; trivial
    simp at this
