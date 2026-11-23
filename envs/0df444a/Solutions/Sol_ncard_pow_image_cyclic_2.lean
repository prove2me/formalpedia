-- Prove2me | solution 2 for ncard_pow_image_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:19:44.384245+00:00
-- url     : https://prove2.me/submissions/4c7136d9-e317-4e18-93c8-4aaac221f28a

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
import Theorems.Thm_ncard_zpowers_eq_orderOf
import Theorems.Thm_ncard_zpowers_pow_image

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {G : Type*} [Group G] (H : Subgroup G) (g : G)
    (hg : H = Subgroup.zpowers g) (m : ℕ) (hH_finite : Set.Finite (H : Set G)) :
    (Set.image (fun x ↦ x ^ m) (H : Set G)).ncard =
    (H : Set G).ncard / Nat.gcd (H : Set G).ncard m := by
  subst hg
  rw [ncard_zpowers_pow_image, ncard_zpowers_eq_orderOf, ncard_zpowers_eq_orderOf]
  exact (finite_zpowers.mp hH_finite).orderOf_pow g m
