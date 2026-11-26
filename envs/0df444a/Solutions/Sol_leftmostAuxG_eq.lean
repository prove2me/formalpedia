-- Prove2me | solution 1 for leftmostAuxG_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:01:48.810671+00:00
-- url     : https://prove2.me/submissions/8723a035-cff3-4dfa-8e77-7b529dbf160d

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree

set_option autoImplicit false
open Set Topology MeasureTheory
open scoped Classical
noncomputable section
variable {X : Type*} [TopologicalSpace X]
omit [TopologicalSpace X]
theorem _root_.solution (F : Set (X × (ℕ → ℕ))) (x : X)
    (h₀ : (closedFiberG F x).Nonempty) :
    ∀ n i, i < n → (leftmostAuxG F x h₀ n).val i = leftmostBranchG F x h₀ i := by
  intro n; induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    simp only [leftmostAuxG, leftmostBranchG]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · rw [Function.update_of_ne (by omega)]; exact ih i h
    · subst h; simp [Function.update_self]
