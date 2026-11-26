-- Prove2me | solution 1 for finishDeviation_injective_off_exceptional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:08:39.803212+00:00
-- url     : https://prove2.me/submissions/1080436e-fbf9-4dae-b64d-9c10699fc76a

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_returnEndpoint_injective

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
noncomputable section
variable {V : Type*} [Fintype V]
variable (d : ℕ) [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] graphAdjDecidable
attribute [local instance] vertexDecidableEq
theorem _root_.solution (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) :
    Set.InjOn (finishDeviation d G hG start rho)
      ((Finset.univ \ exceptionalDeviations d G hG start rho :
        Finset (ValidDeviation d G hG start rho.1 k)) :
          Set (ValidDeviation d G hG start rho.1 k)) := by
  intro q hq r hr hfinish
  have hq' : q ∉ exceptionalDeviations d G hG start rho :=
    (Finset.mem_sdiff.mp hq).2
  have hr' : r ∉ exceptionalDeviations d G hG start rho :=
    (Finset.mem_sdiff.mp hr).2
  apply returnEndpoint_injective d G hG start rho
  rw [finishDeviation_spec d G hG start rho q hq',
    finishDeviation_spec d G hG start rho r hr', hfinish]
