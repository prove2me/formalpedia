-- Prove2me | solution 1 for poly_decompose_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:38:46.028078+00:00
-- url     : https://prove2.me/submissions/e518624c-d8d0-4d62-a7da-05e4d79c34a7

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
omit [DecidableEq F]
theorem _root_.solution (m : ℕ) (hm : m > 0) (p : Polynomial F) (i : Fin m) :
    (poly_decompose m p i).natDegree ≤ p.natDegree / m := by
  rw [Polynomial.natDegree_le_iff_degree_le, Polynomial.degree_le_iff_coeff_zero]
  simp only [poly_decompose, Nat.cast_lt, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range,
    ite_eq_right_iff]
  intro k hk₁ hk₂
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
  nlinarith [Nat.div_add_mod p.natDegree m, Nat.mod_lt p.natDegree hm, Fin.is_lt i]
