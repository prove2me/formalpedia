-- Prove2me | solution 1 for infOcc_comp_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:53:14.441807+00:00
-- url     : https://prove2.me/submissions/459e6b66-2676-483c-9999-c88e2779cac3

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc

set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'
theorem _root_.solution {α β : Type*} {f : α → β} (hf : f.Injective) (xs : Stream' α) :
    InfOcc (f ∘ xs) = f '' InfOcc xs := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨k, -, rfl⟩ := hx.exists
    simpa [InfOcc, hf.eq_iff] using hx
  · rw [Set.image_subset_iff]
    intro x hx
    simpa [InfOcc, hf.eq_iff] using hx
