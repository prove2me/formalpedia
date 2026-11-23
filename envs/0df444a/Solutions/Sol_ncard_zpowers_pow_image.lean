-- Prove2me | solution 1 for ncard_zpowers_pow_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:17:41.826518+00:00
-- url     : https://prove2.me/submissions/091ac535-b28f-447d-b6c6-f4476db4584d

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {G : Type*} [Group G] (g : G) (m : ℕ) :
    (Set.image (fun x ↦ x ^ m) (Subgroup.zpowers g : Set G)).ncard =
    (Subgroup.zpowers (g ^ m) : Set G).ncard := by
  congr 1 with x
  simp only [Set.mem_image, SetLike.mem_coe, Subgroup.mem_zpowers_iff, exists_exists_eq_and]
  exact exists_congr fun k ↦ by group
