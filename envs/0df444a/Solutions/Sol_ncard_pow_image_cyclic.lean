-- Prove2me | solution 1 for ncard_pow_image_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T09:12:21.924576+00:00
-- url     : https://prove2.me/submissions/59a97374-7008-432a-a1b9-87f2cc1d5ee3

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem ncard_pow_image_cyclic {G : Type*} [Group G] (H : Subgroup G) (g : G)
    (hg : H = Subgroup.zpowers g) (m : ℕ) (hH_finite : Set.Finite (H : Set G)) :
    (Set.image (fun x ↦ x ^ m) (H : Set G)).ncard =
    (H : Set G).ncard / Nat.gcd (H : Set G).ncard m := by
  subst hg
  have himg : (fun x : G ↦ x ^ m) '' (Subgroup.zpowers g : Set G) = (Subgroup.zpowers (g ^ m) : Set G) := by
    ext x
    simp only [Set.mem_image, SetLike.mem_coe, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨y, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, by rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]⟩
    · rintro ⟨k, rfl⟩
      exact ⟨g ^ k, ⟨k, rfl⟩, by rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]⟩
  have hfo : IsOfFinOrder g := finite_zpowers.1 hH_finite
  rw [himg, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, SetLike.coe_sort_coe,
    Nat.card_zpowers, Nat.card_zpowers, hfo.orderOf_pow]

theorem solution {G : Type*} [Group G] (H : Subgroup G) (g : G)
    (hg : H = Subgroup.zpowers g) (m : ℕ) (hH_finite : Set.Finite (H : Set G)) :
    (Set.image (fun x ↦ x ^ m) (H : Set G)).ncard =
    (H : Set G).ncard / Nat.gcd (H : Set G).ncard m := by
  subst hg
  have himg : (fun x : G ↦ x ^ m) '' (Subgroup.zpowers g : Set G) = (Subgroup.zpowers (g ^ m) : Set G) := by
    ext x
    simp only [Set.mem_image, SetLike.mem_coe, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨y, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, by rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]⟩
    · rintro ⟨k, rfl⟩
      exact ⟨g ^ k, ⟨k, rfl⟩, by rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]⟩
  have hfo : IsOfFinOrder g := finite_zpowers.1 hH_finite
  rw [himg, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, SetLike.coe_sort_coe,
    Nat.card_zpowers, Nat.card_zpowers, hfo.orderOf_pow]
