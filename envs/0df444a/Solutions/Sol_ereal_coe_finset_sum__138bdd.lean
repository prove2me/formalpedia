-- Prove2me | solution 1 for ereal_coe_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:07:36.011135+00:00
-- url     : https://prove2.me/submissions/902225c9-57c1-4d97-a5f1-92399ff2fa8e

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution {ι : Type*} (s : Finset ι) (f : ι → ENNReal) :
    ((∑ i ∈ s, f i : ENNReal) : EReal) = ∑ i ∈ s, ((f i : ENNReal) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      simp [ha, ih]
