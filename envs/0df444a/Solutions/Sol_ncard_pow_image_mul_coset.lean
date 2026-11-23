-- Prove2me | solution 1 for ncard_pow_image_mul_coset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:17:44.050165+00:00
-- url     : https://prove2.me/submissions/0c28ac46-699c-4735-b80a-55fb1be0b13c

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {G : Type*} [CommGroup G] (H : Subgroup G) (a : G) (m : ℕ) :
    (Set.image (fun x ↦ x ^ m) (Set.image (fun x ↦ a * x) (H : Set G))).ncard =
    (Set.image (fun x ↦ x ^ m) (H : Set G)).ncard := by
  have h_eq : Set.image (fun x ↦ x ^ m) (Set.image (fun x ↦ a * x) (H : Set G)) =
              Set.image (fun y ↦ a ^ m * y) (Set.image (fun x ↦ x ^ m) (H : Set G)) := by
    simp only [← Set.image_comp]
    congr 1 with x
    exact mul_pow a x m
  rw [h_eq, Set.ncard_image_of_injective]
  exact mul_right_injective (a ^ m)
