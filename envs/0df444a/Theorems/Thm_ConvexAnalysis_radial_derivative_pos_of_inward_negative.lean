-- Prove2me | Theorems.Thm_ConvexAnalysis_radial_derivative_pos_of_inward_negative
-- name    : ConvexAnalysis.radial_derivative_pos_of_inward_negative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-30T00:10:32.153027+00:00
-- url     : https://prove2.me/theorems/55795345-ff11-46c9-9666-1e80edda0817
-- title:
--   Inward negativity and tangential curvature force an outward positive derivative
-- statement:
--   Let E be a real normed vector space and s a nonzero vector. Let F:E to R be C2 at s, with F(s)=0 and F(ts)<0 for every 0<=t<1. Assume that the Hessian is positive on every nonzero vector annihilated by DF(s). Then
--   $$DF(s)[s]>0.$$
--   This provides radial transversality from inward sign information and tangential curvature, without assuming regularity of the level set separately. It applies in arbitrary dimension.
-- source:
--   Original normed-space generalization of helper 'radial_derivative_positive' in the accepted proof of BirkhoffGlobalSection.radial_filling_locally_convex_at_each_point, submission 0e9512c6-f3a9-4bf7-9a12-f44fda8605af, https://prove2.me/api/v1/submissions/0e9512c6-f3a9-4bf7-9a12-f44fda8605af/solution. This is an extracted supporting theorem, not a verbatim statement from Joung--van Koert.

import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Basic
open scoped Topology

theorem ConvexAnalysis.radial_derivative_pos_of_inward_negative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ) (s : E)
    (hsne : s ≠ 0) (hc : ContDiffAt ℝ 2 F s) (hzero : F s = 0)
    (hneg : ∀ t : ℝ, 0 ≤ t → t < 1 → F (t • s) < 0)
    (hcurv : ∀ v : E, v ≠ 0 → fderiv ℝ F s v = 0 →
      0 < fderiv ℝ (fun x => fderiv ℝ F x v) s v) :
    0 < fderiv ℝ F s s := by sorry
