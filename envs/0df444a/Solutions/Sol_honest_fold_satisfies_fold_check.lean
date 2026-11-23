-- Prove2me | solution 1 for honest_fold_satisfies_fold_check
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:40:57.446959+00:00
-- url     : https://prove2.me/submissions/b7720f0a-04e5-4d8d-895d-7cb099fdf10f

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness
import Theorems.Thm_honest_fold_eq_fold

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (i : Fin P.num_foldings)
    (f : FRI_domain P i → F) (alpha : F) (z : F)
    (hz : z ∈ FRI_domain P (i + 1)) :
    Fold (FRI_domain P i) (P.m i) (extend_by_zero (FRI_domain P i) f) alpha z =
    extend_by_zero (FRI_domain P (i + 1)) (FRI_honest_fold P i f alpha) z := by
  simp only [extend_by_zero, hz, ↓reduceDIte, honest_fold_eq_fold]
