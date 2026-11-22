-- Prove2me | solution 1 for map_pi_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:44:49.292673+00:00
-- url     : https://prove2.me/submissions/0a088f60-a471-49e3-a0cb-cf967b5d2741

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Definitions.Def_Polychromatic_ForMathlib_Misc

set_option autoImplicit true
open Finset
open MeasureTheory Measure ProbabilityTheory
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : ι → Measure Ω}
variable [∀ i, IsProbabilityMeasure (P i)] {s : Set ι}
open Classical
theorem _root_.solution (i₁ : Set ι) :
    (Measure.pi P).map i₁.restrict = Measure.pi (fun i : i₁ ↦ P i) := by
  apply (Measure.pi_eq _).symm
  intro t hs
  erw [Measure.map_apply i₁.measurable_restrict (.pi Set.countable_univ (by simp [hs]))]
  have : (i₁.restrict ⁻¹' (Set.univ : Set i₁).pi t : Set (ι → Ω)) =
      Set.univ.pi fun i ↦ if h : i ∈ i₁ then t ⟨_, h⟩ else Set.univ := by
    ext f
    simp [Set.restrict, Set.domRestrict, Set.mem_pi]
    constructor
    · intro h i
      split_ifs with hi
      · exact h i hi
      · trivial
    · intro h i hi
      simpa [hi] using h i
  calc
    Measure.pi P (i₁.restrict ⁻¹' Set.univ.pi t)
      = ∏ i, P i (if h : i ∈ i₁ then t ⟨i, h⟩ else Set.univ) := by rw [this, Measure.pi_pi]
    _ = ∏ i, if h : i ∈ i₁ then P i (t ⟨i, h⟩) else 1 := by simp [apply_dite (P _)]
    _ = _ := (Finset.prod_bij_ne_one (fun i _ _ ↦ i.1) (by simp) (by simp) (by simp) (by simp)).symm
