-- Prove2me | solution 1 for reconstruction_local_agreement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:40:54.63805+00:00
-- url     : https://prove2.me/submissions/13d0282f-0e99-4f5a-8589-29977a19a409

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
import Theorems.Thm_reconstruction_from_components

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (m : ℕ) (hm : m > 0) (f : F → F) (S : Finset F) (hS : S ⊆ D)
    (u : Fin m → F → F)
    (hu : ∀ i, ∀ z ∈ pow_domain S m, folding_component D m f i z = u i z) :
    ∀ y ∈ S, f y = reconstruct_func m u y := by
  intro y hy
  rw [reconstruction_from_components D m hm f y (hS hy), reconstruct_func]
  exact Finset.sum_congr rfl fun i _ => hu i (y ^ m) (Finset.mem_image_of_mem _ hy) ▸ rfl
