-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_convex_positive_shift_right_secant_limit
-- name    : AvramDividend.Classical.esscher_convex_positive_shift_right_secant_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:24:04.09161+00:00
-- url     : https://prove2.me/theorems/77e93571-0f3f-403a-8f8e-1c862f249b82
-- title:
--   Convex Laplace-type exponent has a finite right-shift secant limit at every positive interior point
-- statement:
--   For any genuine real convex function f on [0,∞) and any φ>0, the shifted secant quotient (f(φ+h)-f(φ))/h tends to the finite Mathlib right derivative derivWithin f (Ioi φ) φ as h↓0. This does not presuppose a full two-sided HasDerivAt or differentiate the Lévy–Khintchine jump integral; it follows from the pinned convex one-sided derivative theorem and the exact slope reformulation. When a source-specific convexity proof for the actual Lévy Laplace exponent is available, it supplies the finite positive Esscher tilted slope needed for C1 root quotient asymptotics without a full derivative premise.
-- source:
--   Pinned Mathlib ConvexOn.hasDerivWithinAt_rightDeriv_of_mem_interior, hasDerivWithinAt_iff_tendsto_slope, slope_def_field. No Wiener–Hopf scalar assumed.

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.Basic
import Mathlib.LinearAlgebra.AffineSpace.Slope
open Filter Set

theorem AvramDividend.Classical.esscher_convex_positive_shift_right_secant_limit
    (f : ℝ → ℝ) (φ : ℝ) (hφ : 0 < φ)
    (hconv : ConvexOn ℝ (Ici (0 : ℝ)) f) :
    Tendsto (fun h : ℝ => (f (φ + h) - f φ) / h)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (derivWithin f (Ioi φ) φ)) := by sorry
