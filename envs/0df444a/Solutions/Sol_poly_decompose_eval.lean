-- Prove2me | solution 1 for poly_decompose_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:40:35.404806+00:00
-- url     : https://prove2.me/submissions/3a7c8a1b-7a08-4977-ae71-ddd1d4b084e2

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness
import Theorems.Thm_poly_decompose_reconstruct

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
omit [DecidableEq F]
theorem _root_.solution (m : ℕ) (hm : m > 0) (p : Polynomial F) (y : F) :
    p.eval y = ∑ i : Fin m, (poly_decompose m p i).eval (y ^ m) * y ^ (i : ℕ) := by
  conv_lhs => rw [poly_decompose_reconstruct m hm p]
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_pow, Polynomial.eval_X]
