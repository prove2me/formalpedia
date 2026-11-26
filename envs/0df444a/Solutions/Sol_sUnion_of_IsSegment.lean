-- Prove2me | solution 1 for sUnion_of_IsSegment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:46:01.377584+00:00
-- url     : https://prove2.me/submissions/a37c35bd-14d8-4b26-b2f0-2cea80971887

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution

set_option autoImplicit true
variable {α : Type*}
open Set IsChain
variable [PartialOrder α]
theorem _root_.solution {F : Set (Set α)} (hF : ∀M ∈ F, M ⊑ C) : ⋃₀ F ⊑ C := by
  constructor
  · intro s sInUnionF
    obtain ⟨M, MinF, sinM⟩ := sInUnionF
    exact (hF M MinF).1 sinM
  · intro c cinC s sInUnionF cles
    obtain ⟨M, MinF, sinM⟩ := sInUnionF
    exact ⟨M, MinF, (hF M MinF).2 c cinC s sinM cles⟩
