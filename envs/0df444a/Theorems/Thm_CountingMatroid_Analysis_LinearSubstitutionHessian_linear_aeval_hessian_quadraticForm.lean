-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_LinearSubstitutionHessian_linear_aeval_hessian_quadraticForm
-- name    : CountingMatroid.Analysis.LinearSubstitutionHessian.linear_aeval_hessian_quadraticForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:29:14.921715+00:00
-- url     : https://prove2.me/theorems/4a64af6f-1622-4369-b633-fc64f63731c0
-- title:
--   The constant-Hessian quadratic form is pulled back by the substitution
-- statement:
--   Let $\sigma,\tau$ be finite sets, let $A\in\mathbb Q^{\sigma\times\tau}$, and let $p\in\mathbb Q[x_s:s\in\sigma]$. Regard $A$ as a real linear map $\mathbb R^\tau\to\mathbb R^\sigma$. Let $H_p$ be the real matrix of constant coefficients of $\partial_s\partial_t p$, and set $Q_p(v)=v^{\mathsf T}H_pv$. Then substitution by $x=Ay$ gives the equality of real quadratic forms $$Q_{p\circ A}=Q_p\circ A,$$ or, pointwise, $$Q_{p\circ A}(v)=Q_p(Av)\qquad(v\in\mathbb R^\tau).$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/LinearSubstitutionHessian.lean#L68-L96

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

namespace CountingMatroid.Analysis.LinearSubstitutionHessian
end CountingMatroid.Analysis.LinearSubstitutionHessian
namespace CountingMatroid.Analysis.LinearPolynomialChainRule
end CountingMatroid.Analysis.LinearPolynomialChainRule
set_option autoImplicit false

/-!
Linear substitutions pull back the Hessian quadratic form by their transpose
on variable values. This identity holds for arbitrary rational polynomials,
including zero substitution columns and identified variables. It provides
the algebraic part of the substitution closure in the quadratic argument.
-/

namespace CountingMatroid.Analysis.LinearSubstitutionHessian
end CountingMatroid.Analysis.LinearSubstitutionHessian
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.LinearSubstitutionHessian

open scoped BigOperators

theorem CountingMatroid.Analysis.LinearSubstitutionHessian.linear_aeval_hessian_quadraticForm {σ τ : Type} [Fintype σ] [Fintype τ]
    [DecidableEq σ] [DecidableEq τ] (a : σ → τ → ℚ) (p : MvPolynomial σ ℚ) :
    Matrix.toQuadraticForm' (fun i j => ((MvPolynomial.constantCoeff
      (MvPolynomial.pderiv i (MvPolynomial.pderiv j
        (MvPolynomial.aeval
          (fun s => ∑ t, MvPolynomial.C (a s t) * MvPolynomial.X t) p))) : ℚ) : ℝ)) =
    (Matrix.toQuadraticForm' (fun s t => ((MvPolynomial.constantCoeff
      (MvPolynomial.pderiv s (MvPolynomial.pderiv t p)) : ℚ) : ℝ))).comp
        (Matrix.toLin' (fun s t => (a s t : ℝ))) := by sorry
