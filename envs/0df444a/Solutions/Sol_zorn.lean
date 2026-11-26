-- Prove2me | solution 1 for zorn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:49:12.710825+00:00
-- url     : https://prove2.me/submissions/ad03b46e-01c4-420e-879c-12260e2eb87b

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
import Theorems.Thm_unbounded_chain

set_option autoImplicit true
variable {α : Type*}
open Set IsChain
open ChainBounding
theorem _root_.solution [PartialOrder α] [Inhabited α]
    (ind : ∀ (C : Set α), IsChain (· ≤ ·) C → ∃ ub, ∀ a ∈ C, a ≤ ub) : ∃ (x : α), IsMaximal x := by
  obtain ⟨C, chain, subd⟩ := unbounded_chain (α := α)
  push Not at subd
  obtain ⟨ub, hub⟩ := ind C chain
  existsi ub
  intro z hz
  by_contra zneub
  obtain ⟨a, ainC, anltz⟩ := subd z
  exact anltz $ lt_of_le_of_lt (hub a ainC) $ lt_of_le_of_ne' hz zneub
