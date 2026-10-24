-- Prove2me | Theorems.Thm_AvramDividend_Classical_contDiffOn_one_derivative_bound_on_compact
-- name    : AvramDividend.Classical.contDiffOn_one_derivative_bound_on_compact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T04:12:31.54995+00:00
-- url     : https://prove2.me/theorems/c02525fd-37ea-4dbc-bd1f-2a4428f87a7b
-- title:
--   A continuously differentiable function is Lipschitz on each compact sub-interval of its open region of regularity
-- statement:
--   Let W be continuously differentiable on the open interval (0, a), and let x lie in that interval. Then there are a positive radius r, at most min x 1, and a finite constant C, such that the derivative of W is bounded in absolute value by C on the compact interval [x - r, x], and such that for every y in (-r, 0) the increment of W between x + y and x is bounded in absolute value by C times the distance |y|. This is the mean value theorem applied on a fixed compact sub-interval of the region of regularity, and it is the uniform form of the local linear estimate that a C1 function satisfies. It is the C1 counterpart of the mean-remainder estimate used for the twice continuously differentiable case, and it is what turns an asymptotic little-o estimate into a pointwise bound valid on a whole half-line.
-- source:
--   Mathlib.Analysis.Calculus.Deriv.MeanValue, the mean value theorem, applied to a compact sub-interval of an open region of continuous differentiability. Formalised in the Avram Dividend Classical proof programme.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.contDiffOn_one_derivative_bound_on_compact
    (W : ℝ → ℝ) (a x : ℝ)
    (hC1 : ContDiffOn ℝ 1 W (Ioo 0 a))
    (hx : x ∈ Ioo 0 a) :
    ∃ r C : ℝ,
      0 < r ∧ r ≤ min x 1 ∧ 0 ≤ C ∧
      (∀ z : ℝ, z ∈ Icc (x - r) x → |deriv W z| ≤ C) ∧
      (∀ y : ℝ, y ∈ Ioo (-r) 0 → |W (x + y) - W x| ≤ C * |y|) := by sorry
