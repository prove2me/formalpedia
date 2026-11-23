-- Prove2me | solution 1 for pow_domain_is_coset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:19:39.380934+00:00
-- url     : https://prove2.me/submissions/2fa902ec-05ea-43e4-9fcb-806c9e95c030

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F] {D : Finset F} {m : ℕ}
    (h : IsFoldable D m) :
    ∃ (H' : Subgroup Fˣ) (a' : Fˣ),
      (pow_domain D m : Set F) = (a' • (H' : Set Fˣ)).image (fun (x : Fˣ) ↦ (x : F)) := by
  obtain ⟨H, a, hD, hdiv⟩ := h
  use H.map (zpowGroupHom m), a ^ m
  ext z
  simp only [pow_domain, Finset.coe_image, Set.mem_image, hD]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hy
    simp only [Set.mem_smul_set, SetLike.mem_coe] at hu
    obtain ⟨h', hH, rfl⟩ := hu
    simp only [Set.mem_smul_set, SetLike.mem_coe, Subgroup.mem_map, zpowGroupHom_apply]
    refine ⟨(a * h') ^ m, ⟨h' ^ m, ⟨h', hH, ?_⟩, ?_⟩, rfl⟩
    · simp
    · ext; simp [mul_pow]
  · rintro ⟨w, hw, hwz⟩
    simp only [Set.mem_smul_set, SetLike.mem_coe, Subgroup.mem_map, zpowGroupHom_apply,
      zpow_natCast] at hw
    obtain ⟨y', ⟨h', hH, hy'⟩, hw'⟩ := hw
    have hw'' : (a : F) ^ m * (y' : F) = (w : F) := by simp [← hw']
    refine ⟨(a * h' : F), ⟨a * h', ?_, rfl⟩, ?_⟩
    · simpa only [Set.mem_smul_set, SetLike.mem_coe] using ⟨h', hH, by ext; simp⟩
    · simp only [← hwz, ← hw'', ← hy', mul_pow, Units.val_pow_eq_pow_val]
