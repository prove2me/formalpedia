-- Prove2me | solution 2 for fold_eq_sum_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:22:09.552991+00:00
-- url     : https://prove2.me/submissions/c950c945-2a19-486d-8bef-3cac4b2945bb

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
import Theorems.Thm_degree_interpolate_lt_m

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F] (D : Finset F) (m : ℕ)
    (hm : m > 0) (f : F → F) (alpha : F) (z : F) :
    Fold D m f alpha z = ∑ i : Fin m, (alpha ^ (i : ℕ)) * folding_component D m f i z := by
  rw [Fold, Polynomial.eval_eq_sum_range']
  · rw [Finset.sum_range, Finset.sum_congr rfl]
    intro _ _; ring!
  · by_cases hp : Lagrange.interpolate (Block D m z) id f = 0
    · simp [hp, hm]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp).mpr (degree_interpolate_lt_m D m hm f z)
