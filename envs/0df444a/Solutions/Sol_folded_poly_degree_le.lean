-- Prove2me | solution 1 for folded_poly_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:40:04.59386+00:00
-- url     : https://prove2.me/submissions/0a66a4c3-6fd8-462c-ab1b-d879bb102b19

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness
import Theorems.Thm_poly_decompose_degree_le

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
omit [DecidableEq F]
theorem _root_.solution (m : ℕ) (hm : m > 0) (p : Polynomial F) (alpha : F) :
    (folded_poly m p alpha).natDegree ≤ p.natDegree / m :=
  Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ ↦
    (Polynomial.natDegree_C_mul_le ..).trans (poly_decompose_degree_le m hm p i)
