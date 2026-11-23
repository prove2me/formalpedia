-- Prove2me | solution 2 for reconstruction_from_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:26:02.90693+00:00
-- url     : https://prove2.me/submissions/ad086996-45bc-481a-9118-cb99583bd4eb

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
import Theorems.Thm_fold_eq_sum_components

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F] (D : Finset F) (m : ℕ)
    (hm : m > 0) (f : F → F) (y : F) (hy : y ∈ D) :
    f y = ∑ i : Fin m, folding_component D m f i (y ^ m) * y ^ (i : ℕ) := by
  convert fold_eq_sum_components D m hm f y (y ^ m) using 1
  · unfold Fold
    exact (Lagrange.eval_interpolate_at_node f (Set.injOn_id _)
      (Finset.mem_filter.mpr ⟨hy, by grind⟩)).symm
  · grind
