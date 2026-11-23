-- Prove2me | solution 1 for fold_eq_folded_poly_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:43:41.941824+00:00
-- url     : https://prove2.me/submissions/aaa48109-49e1-4de8-bd68-9776b784e2d4

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness
import Theorems.Thm_poly_decompose_eval
import Theorems.Thm_card_block_eq_m_of_foldable
import Theorems.Thm_Lagrange_interpolate_eq_of_degree_lt


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (D : Finset F) (m : ℕ) (hm : m > 0)
    (p : Polynomial F) (alpha : F) (z : F) (hz : z ∈ pow_domain D m)
    (h_foldable : IsFoldable D m) :
    Fold D m (fun x ↦ p.eval x) alpha z = (folded_poly m p alpha).eval z := by
  have h_interpolate : Lagrange.interpolate (Block D m z) id (fun x ↦ Polynomial.eval x p) =
      ∑ i : Fin m, Polynomial.C ((poly_decompose m p i).eval z) * Polynomial.X ^ (i : ℕ) := by
    apply Lagrange.interpolate_eq_of_degree_lt
    · refine (Polynomial.degree_sum_le _ _).trans_lt ?_
      refine (Finset.sup_le (a := ↑(m - 1)) ?_).trans_lt ?_
      · exact fun i _ ↦ (Polynomial.degree_C_mul_X_pow_le _ _).trans
          (WithBot.coe_le_coe.mpr (Nat.le_pred_of_lt i.2))
      · simp only [card_block_eq_m_of_foldable D m hm z hz h_foldable, hm, Nat.cast_lt,
          tsub_lt_self_iff, zero_lt_one, and_self]
    · intro x hx
      simp [Polynomial.eval_finset_sum, (Finset.mem_filter.mp hx).2, poly_decompose_eval m hm p x]
  simp only [Fold, folded_poly, h_interpolate, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, map_pow, mul_comm]
