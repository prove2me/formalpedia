-- Prove2me | solution 1 for homothety_apply_eq_const_add_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:05:46.853895+00:00
-- url     : https://prove2.me/submissions/25cee97f-3d5e-44a8-9e01-392aa731c775

import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine
import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Definitions.Def_Operator_Crouzeix_SmoothJordanSimilarity

set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
theorem _root_.solution (c z : ℂ) (r : ℝ) :
    AffineMap.homothety c r z = (1 - r) • c + (r : ℂ) * z := by
  rw [AffineMap.homothety_apply]
  change (r : ℂ) * (z - c) + c =
    ((1 - r : ℝ) : ℂ) * c + (r : ℂ) * z
  push_cast
  ring
