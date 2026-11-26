-- Prove2me | solution 1 for exceptionalDartCode_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:07:10.40532+00:00
-- url     : https://prove2.me/submissions/1cd873a6-065c-4c4e-8dab-2b0aee6fd3ee

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution

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
    (rho : RotationSystem d V) (k : ℕ) :
    Function.Injective (exceptionalDartCode d G hG start rho k) := by
  rintro ⟨⟨et,⟨eh,he⟩⟩,hem⟩ ⟨⟨ft,⟨fh,hf⟩⟩,hfm⟩ hcode
  apply Subtype.ext
  have hhead : eh = fh := congrArg (fun q ↦ (q.1 : V)) hcode
  subst fh
  have hport := congrArg Prod.snd hcode
  change neighborPorts d G hG eh ⟨et,he.symm⟩ =
    neighborPorts d G hG eh ⟨ft,hf.symm⟩ at hport
  have htail : et = ft := congrArg Subtype.val
    ((neighborPorts d G hG eh).injective hport)
  subst ft
  rfl
