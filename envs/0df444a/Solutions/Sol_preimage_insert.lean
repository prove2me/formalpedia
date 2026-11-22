-- Prove2me | solution 1 for preimage_insert
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T21:09:40.692996+00:00
-- url     : https://prove2.me/submissions/257305bf-d2b6-4558-8bff-82da31472557

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_Family_Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Definitions.Def_EventStructures_Prime_Configuration
set_option autoImplicit true
variable {L : Type*} (es : PES L)

theorem preimage_insert {α β : Type*} {ι : α → β} (hι : Function.Injective ι)
    (c : Set β) (x : α) : {y | ι y ∈ c ∪ {ι x}} = {y | ι y ∈ c} ∪ {x} := by
  ext y
  simp [hι.eq_iff]

theorem solution {α β : Type*} {ι : α → β} (hι : Function.Injective ι)
    (c : Set β) (x : α) : {y | ι y ∈ c ∪ {ι x}} = {y | ι y ∈ c} ∪ {x} :=
  preimage_insert hι c x
