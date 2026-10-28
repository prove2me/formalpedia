-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_LinearSubstitutionHessian_linear_aeval_hessian
-- name    : CountingMatroid.Analysis.LinearSubstitutionHessian.linear_aeval_hessian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:26:45.985137+00:00
-- url     : https://prove2.me/theorems/4e5c6a37-c5a5-4c08-bb99-1a8f4ad0ec86
-- title:
--   The constant Hessian under linear substitution
-- statement:
--   Let $\sigma,\tau$ be finite sets, $A=(a_{st})\in\mathbb Q^{\sigma\times\tau}$, and $p\in\mathbb Q[x_s:s\in\sigma]$. Write $[1]f$ for the constant coefficient of a polynomial $f$, and substitute $x=Ay$. For all $i,j\in\tau$, $$[1]\partial_{y_i}\partial_{y_j}p(Ay)=\sum_{s,t\in\sigma}a_{si}\,([1]\partial_{x_s}\partial_{x_t}p)\,a_{tj}.$$ Equivalently, the Hessians evaluated at the origin satisfy $H_{p\circ A}(0)=A^{\mathsf T}H_p(0)A$.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/LinearSubstitutionHessian.lean#L31-L53

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

theorem CountingMatroid.Analysis.LinearSubstitutionHessian.linear_aeval_hessian {σ τ : Type} [Fintype σ] [Fintype τ]
    (a : σ → τ → ℚ) (p : MvPolynomial σ ℚ) (i j : τ) :
    MvPolynomial.constantCoeff
      (MvPolynomial.pderiv i (MvPolynomial.pderiv j
        (MvPolynomial.aeval
          (fun s => ∑ t, MvPolynomial.C (a s t) * MvPolynomial.X t) p))) =
    ∑ s, ∑ t, a s i *
      MvPolynomial.constantCoeff (MvPolynomial.pderiv s (MvPolynomial.pderiv t p)) *
        a t j := by sorry
