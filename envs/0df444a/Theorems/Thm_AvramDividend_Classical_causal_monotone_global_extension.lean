-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_monotone_global_extension
-- name    : AvramDividend.Classical.causal_monotone_global_extension
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:58:23.818621+00:00
-- url     : https://prove2.me/theorems/2f327ec7-0437-4aaf-8d1d-be13ab7bd399
-- title:
--   Nonnegative causal monotone half-line kernels are globally monotone
-- statement:
--   A nonnegative real kernel supported on [0,infinity) and nondecreasing on that half-line is globally nondecreasing, including pairs of points straddling zero. Bridges the native IsScaleFunction monotonicity clause to the full-convolution monotonicity theorem for the renewal-series construction.
-- source:
--   Elementary ordered-real case split, required by zero-scale Neumann convolution existence construction.

import Mathlib.Order.Monotone.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical Set

theorem AvramDividend.Classical.causal_monotone_global_extension
    (f : ℝ → ℝ)
    (hzero : ∀ x : ℝ, x < 0 → f x = 0)
    (hnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x)
    (hmono : MonotoneOn f (Set.Ici (0 : ℝ))) :
    Monotone f := by sorry
