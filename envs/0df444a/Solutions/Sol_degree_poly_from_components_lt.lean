-- Prove2me | solution 1 for degree_poly_from_components_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:20:57.841693+00:00
-- url     : https://prove2.me/submissions/833d77b2-4794-49db-a7b1-70cfad130a39

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F]
    (m : ℕ) (d : ℕ) (hm : m > 0)
    (P_i : Fin m → Polynomial F)
    (h_deg : ∀ i, (P_i i).degree < d / m) :
    (poly_from_components m P_i).degree < d := by
  rw [poly_from_components]
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff]
  · intro i _
    have h_deg_i := h_deg i
    by_cases hP_i : P_i i = 0
    · simp_all only [gt_iff_lt, Finset.mem_univ, degree_zero, zero_comp, zero_mul]
      exact WithBot.bot_lt_coe _
    · simp_all only [gt_iff_lt, Finset.mem_univ, ne_eq, not_false_eq_true,
        degree_eq_natDegree, Nat.cast_lt, degree_mul, pow_eq_zero_iff', X_ne_zero, false_and,
        natDegree_pow, natDegree_X, mul_one]
      rw [Polynomial.degree_eq_natDegree]
      · rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_pow]
        norm_cast
        nlinarith [Nat.div_mul_le_self d m, Fin.is_lt i]
      · rw [← Polynomial.expand_eq_comp_X_pow, Polynomial.expand_ne_zero hm]
        exact hP_i
  · exact WithBot.bot_lt_coe d
