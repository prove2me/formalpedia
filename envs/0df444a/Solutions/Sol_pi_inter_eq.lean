-- Prove2me | solution 1 for pi_inter_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:44:55.851569+00:00
-- url     : https://prove2.me/submissions/e631aab0-841a-45be-b803-6c9ddf4b1045

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Theorems.Thm_pi_restrict_inter_restrict_eq
import Theorems.Thm_MeasurableSet_of_restrict_preimage

set_option autoImplicit true
open Finset
open MeasureTheory Measure ProbabilityTheory
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : ι → Measure Ω}
variable [∀ i, IsProbabilityMeasure (P i)] {s : Set ι}
theorem _root_.solution (s t : Set ι) (hst : Disjoint s t)
    (A B : Set (ι → Ω)) (hs : DependsOn (· ∈ A) s) (ht : DependsOn (· ∈ B) t)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measure.pi P (A ∩ B) = Measure.pi P A * Measure.pi P B := by
  obtain rfl | hAne := A.eq_empty_or_nonempty
  · simp
  obtain rfl | hBne := B.eq_empty_or_nonempty
  · simp
  obtain ⟨A', rfl⟩ : ∃ A', A = s.restrict ⁻¹' A' := dependsOn_iff_exists_comp.1 hs
  obtain ⟨B', rfl⟩ : ∃ B', B = t.restrict ⁻¹' B' := dependsOn_iff_exists_comp.1 ht
  rw [pi_restrict_inter_restrict_eq hst]
  · exact hA.of_restrict_preimage hAne
  · exact hB.of_restrict_preimage hBne
