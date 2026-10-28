-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_BinaryRankWeightSignature_binary_form_nonpositive_hyperplane
-- name    : CountingMatroid.Analysis.BinaryRankWeightSignature.binary_form_nonpositive_hyperplane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:45:44.211238+00:00
-- url     : https://prove2.me/theorems/bd286c8d-520e-4b91-aec3-248f67d7ebe0
-- title:
--   A binary quadratic form is nonpositive on a linear kernel
-- statement:
--   Let $V$ be a real vector space, let $z,x,y:V\to\mathbb R$ be linear functionals, and let $b,c,d\in\mathbb R$ satisfy $b>0$, $c>0$, and $0\le d\le bc$. Define $$Q(v)=2z(v)^2+2b\,z(v)x(v)+2c\,z(v)y(v)+2d\,x(v)y(v).$$ Then there exists a linear functional $\lambda$ such that $$\lambda(v)=0\ \Longrightarrow\ Q(v)\le0\quad\text{for every }v\in V.$$ The functional is allowed to be zero, so its kernel need not have codimension one. This kernel criterion supports subsequent quadratic-signature arguments.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/BinaryRankWeightSignature.lean#L19-L49

import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature

namespace CountingMatroid.Analysis.BinaryRankWeightSignature
end CountingMatroid.Analysis.BinaryRankWeightSignature
set_option autoImplicit false

/-!
The two-element rank-weight signature calculation. Submodularity bounds the
pair coefficient by the product of the singleton coefficients. The resulting
quadratic has a nonpositive hyperplane, as seen by completing two squares.
-/

namespace CountingMatroid.Analysis.BinaryRankWeightSignature
end CountingMatroid.Analysis.BinaryRankWeightSignature
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BinaryRankWeightSignature

open QuadraticNonpositiveHyperplane
open scoped BigOperators

theorem CountingMatroid.Analysis.BinaryRankWeightSignature.binary_form_nonpositive_hyperplane {V : Type} [AddCommGroup V] [Module ℝ V]
    (z x y : V →ₗ[ℝ] ℝ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 ≤ d) (hbc : d ≤ b * c) :
    HasNonpositiveHyperplane
      ((2 : ℝ) • QuadraticMap.linMulLin z z + (2 * b) • QuadraticMap.linMulLin z x +
        (2 * c) • QuadraticMap.linMulLin z y + (2 * d) • QuadraticMap.linMulLin x y) := by sorry
