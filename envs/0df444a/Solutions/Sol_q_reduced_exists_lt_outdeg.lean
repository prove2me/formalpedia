-- Prove2me | solution 1 for q_reduced.exists_lt_outdeg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:42:17.284798+00:00
-- url     : https://prove2.me/submissions/135d4544-7ddf-4888-ae81-34d125a7d7f6

module
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Definitions.Def_ChipFiringWithLean_Basic

set_option autoImplicit true
@[expose] public section
public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
open Matrix
namespace q_reduced
theorem _root_.solution {G : CFGraph} {q : G.V} {D : CFDiv G}
    (hred : q_reduced G q D) {S : Finset G.V} (hq : q ∉ S) (hS : S.Nonempty) :
    ∃ v ∈ S, D v < outdeg_S G S v := by
  by_contra! h
  exact hred.2 S hq hS h
end q_reduced
