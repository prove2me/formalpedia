-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane_HasNonpositiveHyperplane_nonpos_of_associated_eq_zero
-- name    : CountingMatroid.Analysis.QuadraticNonpositiveHyperplane.HasNonpositiveHyperplane.nonpos_of_associated_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:43:39.892149+00:00
-- url     : https://prove2.me/theorems/ef15a25d-07f1-416a-afd1-896e1b2d15cb
-- title:
--   Nonpositivity orthogonal to a positive vector
-- statement:
--   Let $V$ be a real vector space and $Q$ a real quadratic form with associated symmetric bilinear form $B$, normalized by $B(v,v)=Q(v)$. Assume there exists a linear functional $\ell$ with $Q(v)\le0$ whenever $\ell(v)=0$. For any $e,v\in V$, $$Q(e)>0,\qquad B(e,v)=0\quad\Longrightarrow\quad Q(v)\le0.$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/QuadraticNonpositiveHyperplane.lean#L55-L80

import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature

set_option autoImplicit false

/-!
A quadratic form is nonpositive on a hyperplane if some real linear
functional has a nonpositive kernel. This property survives linear pullback
and nonnegative scaling. It implies the signature bound, and also gives
nonpositivity on the orthogonal complement of any positive vector.
No property of matroid polynomials is assumed or asserted here.
-/

namespace CountingMatroid.Analysis.QuadraticNonpositiveHyperplane
end CountingMatroid.Analysis.QuadraticNonpositiveHyperplane
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.QuadraticNonpositiveHyperplane

theorem CountingMatroid.Analysis.QuadraticNonpositiveHyperplane.HasNonpositiveHyperplane.nonpos_of_associated_eq_zero {V : Type}
    [AddCommGroup V] [Module ℝ V] [Invertible (2 : ℝ)]
    {Q : QuadraticForm ℝ V} (hQ : HasNonpositiveHyperplane Q)
    (e v : V) (he : 0 < Q e) (hv : Q.associated e v = 0) : Q v ≤ 0 := by sorry
