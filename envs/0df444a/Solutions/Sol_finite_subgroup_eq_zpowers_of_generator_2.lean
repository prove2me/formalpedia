-- Prove2me | solution 2 for finite_subgroup_eq_zpowers_of_generator
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T09:01:30.255809+00:00
-- url     : https://prove2.me/submissions/4af86f6e-5c89-4fdd-806b-534ebb0ae8ea

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem finite_subgroup_eq_zpowers_of_generator {G : Type*} [Group G] (H : Subgroup G)
    [Finite H] (g : H) (hg : ∀ x : H, x ∈ Subgroup.zpowers g) :
    H = Subgroup.zpowers (g : G) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  · exact (Subgroup.zpowers_le).mpr g.2

theorem solution {G : Type*} [Group G] (H : Subgroup G)
    [Finite H] (g : H) (hg : ∀ x : H, x ∈ Subgroup.zpowers g) :
    H = Subgroup.zpowers (g : G) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  · exact (Subgroup.zpowers_le).mpr g.2
