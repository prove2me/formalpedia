-- Prove2me | solution 1 for reconstruct_func_in_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:22:06.639357+00:00
-- url     : https://prove2.me/submissions/9ed08333-e19d-4031-8015-60e64b101a0d

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
import Theorems.Thm_degree_reconstruct_poly_lt

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F] (D : Finset F) (m : ℕ) (d : ℕ)
    (u : Fin m → F → F)
    (hu : ∀ i, (pow_domain D m : Set F).restrict (u i) ∈ reedSolomon (pow_domain D m) (d / m)) :
    (D : Set F).restrict (reconstruct_func m u) ∈ reedSolomon D d := by
  choose y hy hy' using hu
  refine ⟨∑ i, Polynomial.comp (y i) (Polynomial.X ^ m) * Polynomial.X ^ (i : ℕ), ?_, ?_⟩
  · simp only [SetLike.mem_coe, mem_degreeLT]
    exact degree_reconstruct_poly_lt m d y fun i ↦ mem_degreeLT.mp (hy i)
  · ext x
    simp_all only [SetLike.mem_coe, pow_domain, evalOn, LinearMap.coe_mk, AddHom.coe_mk,
      map_sum, eval_mul, eval_comp, eval_pow, eval_X, Finset.sum_apply, Set.restrict_apply]
    exact Finset.sum_congr rfl fun i _ ↦
      congrArg (· * (x : F) ^ (i : ℕ)) <|
        congr_fun (hy' i) ⟨(x : F) ^ m, Finset.mem_image_of_mem _ x.2⟩
