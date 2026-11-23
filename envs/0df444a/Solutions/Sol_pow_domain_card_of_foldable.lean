-- Prove2me | solution 1 for pow_domain_card_of_foldable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:40:00.520325+00:00
-- url     : https://prove2.me/submissions/cea7f51b-53fc-4ec7-a891-93093f8d5837

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
import Theorems.Thm_ncard_pow_image_cyclic
import Theorems.Thm_subgroup_finite_of_coset_image_finite
import Theorems.Thm_finite_subgroup_eq_zpowers_of_generator
import Theorems.Thm_pow_domain_card_eq_ncard_pow_image
import Theorems.Thm_subgroup_ncard_eq_finset_card
import Theorems.Thm_ncard_pow_image_smul_coset
import Theorems.Thm_gcd_pow_succ_self
import Theorems.Thm_pow_domain_singleton_card

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (H : Subgroup Fˣ) (a : Fˣ) (m k : ℕ) (hm : m > 0)
    (hD : (D : Set F) = (a • (H : Set Fˣ)).image (fun x ↦ ↑x))
    (hk : D.card = m ^ k) :
    (pow_domain D m).card = m ^ (k - 1) := by
  -- Case split on k
  rcases k with (_ | k)
  · -- k = 0: D is a singleton
    simp only [pow_zero, Nat.zero_sub] at hk ⊢
    rw [Finset.card_eq_one] at hk
    obtain ⟨x, hx⟩ := hk
    rw [hx, pow_domain_singleton_card]
  · -- k > 0: Use the cyclic group formula
    have h_finite : Set.Finite (H : Set Fˣ) := by
      apply subgroup_finite_of_coset_image_finite H a
      exact hD ▸ D.finite_toSet
    have : Finite H := Set.Finite.to_subtype h_finite
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
    let g' := g.val
    have hH_eq : H = Subgroup.zpowers g' := finite_subgroup_eq_zpowers_of_generator H g hg
    simp only [Nat.succ_sub_one]
    have h_pow_eq : (pow_domain D m).card =
        (Set.image (fun x ↦ x ^ m) (a • (H : Set Fˣ))).ncard :=
      pow_domain_card_eq_ncard_pow_image D H a m hD
    have h_smul_eq : (Set.image (fun x ↦ x ^ m) (a • (H : Set Fˣ))).ncard =
        (Set.image (fun x ↦ x ^ m) (H : Set Fˣ)).ncard :=
      ncard_pow_image_smul_coset H a m
    have h_cyclic_formula : (Set.image (fun x ↦ x ^ m) (H : Set Fˣ)).ncard =
        (H : Set Fˣ).ncard / Nat.gcd (H : Set Fˣ).ncard m :=
      ncard_pow_image_cyclic H g' hH_eq m h_finite
    have h_card_H : (H : Set Fˣ).ncard = m ^ (k + 1) := by
      rw [subgroup_ncard_eq_finset_card D H a hD, hk]
    have h_gcd : Nat.gcd (m ^ (k + 1)) m = m := gcd_pow_succ_self m k
    rw [h_pow_eq, h_smul_eq, h_cyclic_formula, h_card_H, h_gcd]
    exact Nat.div_eq_of_eq_mul_left hm rfl
