-- Prove2me | solution 1 for poly_from_components_eval_eq_f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:40:58.199801+00:00
-- url     : https://prove2.me/submissions/6a928ac3-ebde-4c95-b7ad-8c5c60912a5b

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
import Theorems.Thm_eval_poly_from_components
import Theorems.Thm_reconstruction_from_components

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (m : ℕ) (hm : m > 0)
    (f : F → F) (S : Finset F) (hS : S ⊆ D)
    (P_i : Fin m → Polynomial F)
    (h_agree : ∀ i, ∀ z ∈ pow_domain S m, (P_i i).eval z = folding_component D m f i z) :
    ∀ x ∈ S, (poly_from_components m P_i).eval x = f x := by
  intro x hx
  rw [eval_poly_from_components, reconstruction_from_components D m hm f x (hS hx)]
  exact Finset.sum_congr rfl fun i _ =>
    congrArg (· * x ^ (i : ℕ)) (h_agree i _ (Finset.mem_image_of_mem _ hx))
