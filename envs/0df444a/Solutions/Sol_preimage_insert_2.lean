-- Prove2me | solution 2 for preimage_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:11:55.746497+00:00
-- url     : https://prove2.me/submissions/e66809bb-0a53-4a9d-9385-3776463eb936

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_Family_Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Definitions.Def_EventStructures_Prime_Configuration

set_option autoImplicit true
variable {L : Type*} (es : PES L)
theorem _root_.solution {α β : Type*} {ι : α → β} (hι : Function.Injective ι)
    (c : Set β) (x : α) : {y | ι y ∈ c ∪ {ι x}} = {y | ι y ∈ c} ∪ {x} := by
  ext y
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (hι h)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (congrArg ι h)
