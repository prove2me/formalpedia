-- Prove2me | solution 1 for result_129_e7_joint_laws_eq_of_rectangle_masses_measurability_4499f086
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:00:20.13533+00:00
-- url     : https://prove2.me/submissions/4a1805fa-2687-4c49-bf13-ba1e0ffd7b02

import Definitions.Def_auto_M04_6e37b463_SolvesMartingaleProblem
import Definitions.Def_auto_M04_6e37b463_UniformBoundedFunction
import Definitions.Def_auto_M04_6e37b463_processPast
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Continuous
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.UniformSpace.UniformEmbedding
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology
open EthierKurtz Classical
theorem solution
    {ι E Ω Ω' : Type*} [Fintype ι] [MeasurableSpace E]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (x : Ω → ι → E) (y : Ω' → ι → E)
    (hx : Measurable x) (hy : Measurable y)
    (hrect : ∀ B : ι → Set E, (∀ i, MeasurableSet (B i)) →
      P {ω | ∀ i, x ω i ∈ B i} = Q {ω | ∀ i, y ω i ∈ B i}) 
    (hpi : (let rect : (ι → Set E) → Set (ι → E) := (fun B => {z | ∀ i, z i ∈ B i}); let S : Set (Set (ι → E)) := ( {s | ∃ B, (∀ i, MeasurableSet (B i)) ∧ s = rect B}); IsPiSystem S))
    (hSmeas : (let rect : (ι → Set E) → Set (ι → E) := (fun B => {z | ∀ i, z i ∈ B i}); let S : Set (Set (ι → E)) := ( {s | ∃ B, (∀ i, MeasurableSet (B i)) ∧ s = rect B}); ∀ s, s ∈ S → MeasurableSet s))
    : (let rect : (ι → Set E) → Set (ι → E) := (fun B => {z | ∀ i, z i ∈ B i}); let S : Set (Set (ι → E)) := ( {s | ∃ B, (∀ i, MeasurableSet (B i)) ∧ s = rect B}); (inferInstance : MeasurableSpace (ι → E)) =
      MeasurableSpace.generateFrom S) := by
    classical
    let rect : (ι → Set E) → Set (ι → E) := fun B =>
        {z | ∀ i, z i ∈ B i}
    let S : Set (Set (ι → E)) :=
        {s | ∃ B, (∀ i, MeasurableSet (B i)) ∧ s = rect B}
    let T : Set (Set (ι → E)) := {Set.univ}
    apply le_antisymm
    · rw [MeasurableSpace.pi_eq_generateFrom_projections]
      apply (MeasurableSpace.generateFrom_le_iff _).mpr
      rintro s ⟨i, A, hA, rfl⟩
      let B : ι → Set E := fun j => if j = i then A else Set.univ
      have hB : ∀ j, MeasurableSet (B j) := by
        intro j
        by_cases hji : j = i <;> simp [B, hji, hA]
      have hEq : {z : ι → E | z i ∈ A} = rect B := by
        ext z
        constructor
        · intro hz j
          by_cases hji : j = i
          · subst j
            simpa [B] using hz
          · simp [B, hji]
        · intro hz
          simpa [B] using hz i
      exact MeasurableSpace.measurableSet_generateFrom ⟨B, hB, hEq⟩
    · apply (MeasurableSpace.generateFrom_le_iff _).mpr
      exact hSmeas
