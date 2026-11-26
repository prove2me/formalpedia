-- Prove2me | solution 1 for unbounded_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:48:36.681021+00:00
-- url     : https://prove2.me/submissions/6b648a7e-3def-4a9b-8ce7-be2f0d1f12fc

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
import Theorems.Thm_ChainBounding_chain_bounding
import Theorems.Thm_UnboundedChain_f_bounds

set_option autoImplicit true
variable {α : Type*}
open Set IsChain
open ChainBounding
theorem _root_.solution [PartialOrder α] [Inhabited α] :
    ∃ C, IsChain (· ≤ ·) C ∧ ¬ ∃ sb : α, ∀ a ∈ C, a < sb := by
  by_contra strbd; push Not at strbd
  have : UnboundedChain α := ⟨strbd⟩
  have : ChainBounding α := ⟨UnboundedChain.f_bounds (α := α)⟩
  exact chain_bounding (α := α)
