-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_LinearPolynomialChainRule_linear_aeval_comp
-- name    : CountingMatroid.Analysis.LinearPolynomialChainRule.linear_aeval_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:47:49.109988+00:00
-- url     : https://prove2.me/theorems/17596e57-985d-444e-aacd-b64c666b21ef
-- title:
--   Linear polynomial substitutions compose by matrix multiplication
-- statement:
--   Let $\sigma$ be a variable type and let $\tau,\upsilon$ be finite variable types. Let $a:\sigma\times\tau\to\mathbb Q$ and $b:\tau\times\upsilon\to\mathbb Q$. For a polynomial $p\in\mathbb Q[x_s:s\in\sigma]$, first substitute $x_s=\sum_ta_{st}y_t$ and then $y_t=\sum_ub_{tu}z_u$. Then $$p\!\left(x_s\mapsto\sum_ta_{st}\sum_ub_{tu}z_u\right)=p\!\left(x_s\mapsto\sum_u\left(\sum_ta_{st}b_{tu}\right)z_u\right).$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/LinearPolynomialChainRule.lean#L44-L62

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

theorem CountingMatroid.Analysis.LinearPolynomialChainRule.linear_aeval_comp {σ τ υ : Type} [Fintype τ] [Fintype υ]
    (a : σ → τ → ℚ) (b : τ → υ → ℚ) (p : MvPolynomial σ ℚ) :
    MvPolynomial.aeval (fun t => ∑ u, MvPolynomial.C (b t u) * MvPolynomial.X u)
      (MvPolynomial.aeval (fun s => ∑ t, MvPolynomial.C (a s t) * MvPolynomial.X t) p) =
    MvPolynomial.aeval
      (fun s => ∑ u, MvPolynomial.C (∑ t, a s t * b t u) * MvPolynomial.X u) p := by sorry
