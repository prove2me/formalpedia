-- Prove2me | solution 1 for folding_components_in_code_implies_f_in_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:28:55.108354+00:00
-- url     : https://prove2.me/submissions/7da03d53-ea7c-4eb9-a3f9-04aa6e500ba8

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
import Theorems.Thm_degree_poly_from_components_lt
import Theorems.Thm_reconstruction_from_components

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (m : ℕ) (d : ℕ) (hm : m > 0)
    (f : F → F) (S : Finset F) (hS : S ⊆ D)
    (u' : Fin m → (pow_domain D m → F))
    (hu' : ∀ i, u' i ∈ reedSolomon (pow_domain D m) (d / m))
    (h_agree : ∀ i, ∀ z ∈ pow_domain S m, folding_component D m f i z =
      if h : z ∈ pow_domain D m then u' i ⟨z, h⟩ else 0) :
    ∃ u ∈ reedSolomon D d, ∀ (x : F) (hx : x ∈ S), u ⟨x, hS hx⟩ = f x := by
  simp only [reedSolomon, Submodule.mem_map] at hu' ⊢
  choose p hp_deg hp_eq using hu'
  refine ⟨evalOn D (poly_from_components m p), ⟨poly_from_components m p, ?_, rfl⟩, ?_⟩
  · exact Polynomial.mem_degreeLT.mpr <|
      degree_poly_from_components_lt m d hm p fun i ↦ Polynomial.mem_degreeLT.mp (hp_deg i)
  · intro x hx
    have := reconstruction_from_components D m hm f x (hS hx)
    simp_all only [evalOn, LinearMap.coe_mk, AddHom.coe_mk, poly_from_components,
      map_sum, eval_mul, eval_comp, eval_pow, eval_X, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [h_agree i (x ^ m) (Finset.mem_image_of_mem _ hx)]
    simp only [← hp_eq i, dite_eq_ite, ite_mul, zero_mul, left_eq_ite_iff,
      mul_eq_zero, pow_eq_zero_iff', ne_eq]
    exact fun h ↦ absurd (Finset.mem_image_of_mem _ <| hS hx) h
