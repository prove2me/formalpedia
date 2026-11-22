-- Prove2me | solution 1 for pi_restrict_inter_restrict_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:38:34.872182+00:00
-- url     : https://prove2.me/submissions/0caee146-d3ea-41e5-8927-4bf1470e511c

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Theorems.Thm_indepFun_restrict_restrict_pi

set_option autoImplicit true
open Finset
open MeasureTheory Measure ProbabilityTheory
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : ι → Measure Ω}
variable [∀ i, IsProbabilityMeasure (P i)] {s : Set ι}
theorem _root_.solution {s t : Set ι} (hi : Disjoint s t)
    (A : Set (s → Ω)) (B : Set (t → Ω)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measure.pi P (s.restrict ⁻¹' A ∩ t.restrict ⁻¹' B) =
      Measure.pi P (s.restrict ⁻¹' A) * Measure.pi P (t.restrict ⁻¹' B) :=
  (indepFun_restrict_restrict_pi hi (P := P)).measure_inter_preimage_eq_mul A B hA hB
