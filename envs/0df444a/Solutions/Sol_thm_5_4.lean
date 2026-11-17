-- Prove2me | solution 1 for thm_5_4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:23:17.039857+00:00
-- url     : https://prove2.me/submissions/3e639ebd-8500-4ecf-be0d-a2492e31f4ff

import Definitions.Def_ProbabilityTheory_chapter_05_thm_5_4_F000
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic
import Theorems.Thm_thm_5_5


/-
  # Theorem 5.4
  Independence of continuous distributions
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set


theorem solution {Ω : Type _} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) :
    ProbabilityTheory.IndepFun X Y μ ↔
      ∀ x y : ℝ,
        jointCDF μ X Y x y = marginalCDF μ X x * marginalCDF μ Y y := by
  constructor
  · intro hXY x y
    rw [jointCDF, marginalCDF]
    have hpre := (ProbabilityTheory.indepFun_iff_indepSet_preimage (μ := μ) hX hY).1 hXY
    exact
      (ProbabilityTheory.indepSet_iff_measure_inter_eq_mul
        (hX measurableSet_Iic)
        (hY measurableSet_Iic)
        (μ := μ)).1 (hpre (Set.Iic x) (Set.Iic y) measurableSet_Iic measurableSet_Iic)
  · intro hCDF
    let C : Set (Set ℝ) := ⋃ a : ℚ, ({Set.Iic (a : ℝ)} : Set (Set ℝ))
    have hRat :
        ∀ A B, A ∈ C → B ∈ C → ProbabilityTheory.IndepSet (X ⁻¹' A) (Y ⁻¹' B) μ := by
      intro A B hA hB
      rcases Set.mem_iUnion.1 hA with ⟨a, ha⟩
      rcases Set.mem_singleton_iff.1 ha with rfl
      rcases Set.mem_iUnion.1 hB with ⟨b, hb⟩
      rcases Set.mem_singleton_iff.1 hb with rfl
      rw [ProbabilityTheory.indepSet_iff_measure_inter_eq_mul
        (hX measurableSet_Iic) (hY measurableSet_Iic) (μ := μ)]
      simpa [jointCDF, marginalCDF] using hCDF (a : ℝ) (b : ℝ)
    exact thm_5_5 μ X Y hX hY C Real.isPiSystem_Iic_rat Real.borel_eq_generateFrom_Iic_rat hRat