-- Prove2me | solution 1 for degree_reconstruct_poly_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:20:37.811624+00:00
-- url     : https://prove2.me/submissions/64aa6a45-f254-4e2b-bae3-5231f64c79d6

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F] (m : ℕ) (d : ℕ)
    (p : Fin m → Polynomial F) (h : ∀ i, (p i).degree < d / m) :
    (poly_from_components m p).degree < d := by
  refine (degree_sum_le _ _).trans_lt (Finset.sup_lt_iff ?_ |>.2 ?_)
  · exact WithBot.bot_lt_coe d
  · intro i _
    by_cases hi : p i = 0
    · simp only [hi, zero_comp, zero_mul, degree_zero]
      exact WithBot.bot_lt_coe _
    · simp_all only [Finset.mem_univ, degree_mul, degree_pow, degree_X, nsmul_eq_mul, mul_one]
      refine (add_le_add (degree_le_natDegree (p := (p i).comp (X ^ m))) le_rfl).trans_lt ?_
      rw [natDegree_comp, natDegree_X_pow]
      have hnd := by simpa [degree_eq_natDegree hi] using h i
      exact_mod_cast (by nlinarith [Nat.div_mul_le_self d m, hnd, Fin.is_lt i] :
        (natDegree (p i) : ℕ) * m + i < d)
