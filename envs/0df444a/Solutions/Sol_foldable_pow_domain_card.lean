-- Prove2me | solution 1 for foldable_pow_domain_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:25:22.064873+00:00
-- url     : https://prove2.me/submissions/c6444419-44cf-4ccb-97b8-cd4a2c8246f2

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
import Theorems.Thm_ncard_pow_image_cyclic
import Theorems.Thm_subgroup_finite_of_coset_image_finite
import Theorems.Thm_finite_subgroup_eq_zpowers_of_generator
import Theorems.Thm_pow_domain_card_eq_ncard_pow_image
import Theorems.Thm_subgroup_ncard_eq_finset_card
import Theorems.Thm_ncard_pow_image_smul_coset

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (m : ℕ) (h_foldable : IsFoldable D m) :
    D.card = m * (pow_domain D m).card := by
  -- Extract the subgroup H and coset element a from the foldable domain definition
  obtain ⟨H, a, hD, hdiv⟩ := h_foldable
  -- Prove that H is finite
  have h_finite : Set.Finite (H : Set Fˣ) :=
    subgroup_finite_of_coset_image_finite H a (hD ▸ D.finite_toSet)
  have : Finite H := h_finite.to_subtype
  -- Get a generator for the cyclic subgroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  have hH_eq : H = Subgroup.zpowers g.val := finite_subgroup_eq_zpowers_of_generator H g hg
  -- Express D.card in terms of H
  have h_card_H : (H : Set Fˣ).ncard = D.card := subgroup_ncard_eq_finset_card D H a hD
  -- Use the fact that |D^m| = |H| / gcd(|H|, m) = |H| / m (since m | |H|)
  have h_pow_card : (pow_domain D m).card = (H : Set Fˣ).ncard / m := by
    simp only [pow_domain_card_eq_ncard_pow_image D H a m hD, ncard_pow_image_smul_coset,
      ncard_pow_image_cyclic H g.val hH_eq m h_finite, h_card_H ▸ Nat.gcd_eq_right hdiv]
  -- Now conclude
  exact h_pow_card ▸ h_card_H.symm ▸ Nat.eq_mul_of_div_eq_right hdiv rfl
