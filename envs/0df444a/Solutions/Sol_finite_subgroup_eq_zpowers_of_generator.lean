-- Prove2me | solution 1 for finite_subgroup_eq_zpowers_of_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:00:26.669802+00:00
-- url     : https://prove2.me/submissions/d0fba8b6-8848-467b-8144-d787baa968ee

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {G : Type*} [Group G] (H : Subgroup G)
    [Finite H] (g : H) (hg : ∀ x : H, x ∈ Subgroup.zpowers g) :
    H = Subgroup.zpowers (g : G) :=
  le_antisymm (fun _ hx ↦ (hg ⟨_, hx⟩).imp fun _ ↦ congrArg Subtype.val)
    (Subgroup.zpowers_le.mpr g.2)
