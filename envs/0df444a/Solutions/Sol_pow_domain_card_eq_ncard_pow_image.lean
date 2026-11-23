-- Prove2me | solution 1 for pow_domain_card_eq_ncard_pow_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:00:55.442272+00:00
-- url     : https://prove2.me/submissions/4f3dddff-926e-43ff-8886-a572985c7941

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (H : Subgroup Fˣ) (a : Fˣ) (m : ℕ)
    (hD : (D : Set F) = (a • (H : Set Fˣ)).image (fun x : Fˣ ↦ (x : F))) :
    (pow_domain D m).card = (Set.image (fun x : Fˣ ↦ x ^ m) (a • (H : Set Fˣ))).ncard := by
  have h_image_eq : (pow_domain D m : Set F) =
      (Set.image (fun x : Fˣ ↦ x ^ m) (a • (H : Set Fˣ))).image (fun x : Fˣ ↦ (x : F)) := by
    ext z; simp only [pow_domain, Finset.coe_image, Set.mem_image, hD]
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u ^ m, ⟨u, hu, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, ⟨u, hu, rfl⟩, rfl⟩
  rw [← Set.ncard_coe_finset, h_image_eq, Set.ncard_image_of_injective _ Units.val_injective]
