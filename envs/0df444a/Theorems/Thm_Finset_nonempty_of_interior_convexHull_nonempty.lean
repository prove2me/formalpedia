-- Prove2me | Theorems.Thm_Finset_nonempty_of_interior_convexHull_nonempty
-- name    : Finset.nonempty_of_interior_convexHull_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:45:51.88236+00:00
-- url     : https://prove2.me/theorems/ed53acb3-3283-487a-a933-e71608b3e249
-- title:
--   Finset: nonempty of interior convex Hull nonempty
-- statement:
--   A finite point set whose convex hull has nonempty interior is nonempty.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportDomain.lean#L61-L71
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportDomain.lean#L61-L71

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeTight
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff InnerProductSpace

theorem Finset.nonempty_of_interior_convexHull_nonempty
    {u : Finset ℂ}
    (hinterior :
      (interior (convexHull ℝ (u : Set ℂ))).Nonempty) :
    u.Nonempty := by sorry
