-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_LinearPolynomialChainRule_linear_aeval_pderiv
-- name    : CountingMatroid.Analysis.LinearPolynomialChainRule.linear_aeval_pderiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:43:52.548171+00:00
-- url     : https://prove2.me/theorems/4efda3f7-b170-4f5f-9ca9-14dbaf5670d0
-- title:
--   Polynomial chain rule for a rational linear substitution
-- statement:
--   Let $\sigma,\tau$ be finite sets, let $A=(a_{su})_{s\in\sigma,u\in\tau}$ be a rational matrix, and let $p\in\mathbb Q[x_s:s\in\sigma]$. Substitute $x_s=\sum_{u\in\tau}a_{su}y_u$, denoting the resulting polynomial by $p(Ay)$. For every $t\in\tau$, $$\partial_{y_t}p(Ay)=\left(\sum_{s\in\sigma}a_{st}\,\partial_{x_s}p\right)(Ay).$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/LinearPolynomialChainRule.lean#L14-L42

import Mathlib.Algebra.MvPolynomial.PDeriv

namespace CountingMatroid.Analysis.LinearPolynomialChainRule
end CountingMatroid.Analysis.LinearPolynomialChainRule
set_option autoImplicit false

/-!
Formal polynomial calculus for moving derivatives before linear substitutions.
These identities do not assert Lorentzianity or a signature bound.
-/

namespace CountingMatroid.Analysis.LinearPolynomialChainRule
end CountingMatroid.Analysis.LinearPolynomialChainRule
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.LinearPolynomialChainRule

open scoped BigOperators

theorem CountingMatroid.Analysis.LinearPolynomialChainRule.linear_aeval_pderiv {σ τ : Type} [Fintype σ] [Fintype τ]
    (a : σ → τ → ℚ) (p : MvPolynomial σ ℚ) (t : τ) :
    MvPolynomial.pderiv t
      (MvPolynomial.aeval (fun s => ∑ u, MvPolynomial.C (a s u) * MvPolynomial.X u) p) =
    MvPolynomial.aeval (fun s => ∑ u, MvPolynomial.C (a s u) * MvPolynomial.X u)
      (∑ s, MvPolynomial.C (a s t) * MvPolynomial.pderiv s p) := by sorry
