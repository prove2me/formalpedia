-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_QuadraticSignatureHyperplane_hasNonpositiveHyperplane_of_sigPos_le_one
-- name    : CountingMatroid.Analysis.QuadraticSignatureHyperplane.hasNonpositiveHyperplane_of_sigPos_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:47:36.985645+00:00
-- url     : https://prove2.me/theorems/368284f8-51c9-4d50-bbac-9aaaca3229f9
-- title:
--   A positive-signature bound supplies a nonpositive hyperplane
-- statement:
--   Let $V$ be a finite-dimensional real vector space and $Q$ a real quadratic form. Let $\operatorname{sig}_+(Q)$ denote the maximum dimension of a positive-definite subspace. If $$\operatorname{sig}_+(Q)\le1,$$ then $$\exists\ell:V\to\mathbb R\text{ linear},\qquad Q|_{\ker\ell}\le0.$$ The functional is allowed to be zero.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/QuadraticSignatureHyperplane.lean#L17-L60

import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature

namespace CountingMatroid.Analysis.QuadraticSignatureHyperplane
end CountingMatroid.Analysis.QuadraticSignatureHyperplane
set_option autoImplicit false

/-!
Convert an at-most-one-positive signature bound to the linear-functional
witness used by the rank-weight analysis. Mathlib diagonalizes the quadratic
form; deleting its sole positive square leaves a nonpositive kernel.
This module establishes no signature bound for matroid polynomials.
-/

namespace CountingMatroid.Analysis.QuadraticSignatureHyperplane
end CountingMatroid.Analysis.QuadraticSignatureHyperplane
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.QuadraticSignatureHyperplane

open scoped BigOperators
open QuadraticNonpositiveHyperplane

theorem CountingMatroid.Analysis.QuadraticSignatureHyperplane.hasNonpositiveHyperplane_of_sigPos_le_one {V : Type}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (Q : QuadraticForm ℝ V) (hQ : sigPos Q ≤ 1) :
    HasNonpositiveHyperplane Q := by sorry
