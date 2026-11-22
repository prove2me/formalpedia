-- Prove2me | solution 1 for indepFun_restrict_restrict_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:37:57.696174+00:00
-- url     : https://prove2.me/submissions/9fe91c90-2f63-4b6a-9b65-9a6922e65594

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
theorem _root_.solution {s t : Set ι} (hi : Disjoint s t) :
    IndepFun s.restrict t.restrict (Measure.pi P) := by
  lift s to Finset ι using s.toFinite
  lift t to Finset ι using t.toFinite
  simp only [disjoint_coe] at hi
  have : iIndepFun (fun x y ↦ y x) (Measure.pi P) := iIndepFun_pi (X := fun i x ↦ x) (by fun_prop)
  have := this.indepFun_finset s t hi (by fun_prop)
  exact this
