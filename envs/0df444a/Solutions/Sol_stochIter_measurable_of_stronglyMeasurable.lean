-- Prove2me | solution 1 for stochIter_measurable_of_stronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T09:14:15.736963+00:00
-- url     : https://prove2.me/submissions/7786a6c4-cea9-4fd2-ab5a-dd7c53d4983a

import Mathlib
import Definitions.Def_ShorNonsmooth_Stochastic_StochasticSubgradientMethod
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Topology
open scoped InnerProductSpace
open ShorNonsmooth.Stochastic
theorem solution {n : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (ℱ : Filtration ℕ m0) (h : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hh_meas : ∀ j, Measurable (h j))
    (G : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (x₀ : EuclideanSpace ℝ (Fin n))
    (hG_meas : ∀ j, StronglyMeasurable[ℱ (j + 1)] (G j)) (j : ℕ) :
    Measurable[(ℱ j : MeasurableSpace Ω)] (stochIter h G x₀ j) := by
  induction j with
  | zero =>
      simpa only [stochIter] using measurable_const
  | succ j ih =>
      have hGj : Measurable[(ℱ (j + 1) : MeasurableSpace Ω)] (G j) := (hG_meas j).measurable
      have ih' : Measurable[(ℱ (j + 1) : MeasurableSpace Ω)] (stochIter h G x₀ j) :=
        ih.mono (ℱ.mono (by omega)) (le_refl _)
      have hcomp : Measurable[(ℱ (j + 1) : MeasurableSpace Ω)]
          (fun ω => h j (stochIter h G x₀ j ω)) := (hh_meas j).comp ih'
      have hsmul : Measurable[(ℱ (j + 1) : MeasurableSpace Ω)]
          (fun ω => h j (stochIter h G x₀ j ω) • G j ω) := hcomp.smul hGj
      have hsub : Measurable[(ℱ (j + 1) : MeasurableSpace Ω)]
          (fun ω => stochIter h G x₀ j ω - h j (stochIter h G x₀ j ω) • G j ω) :=
        ih'.sub hsmul
      simpa only [stochIter] using hsub
