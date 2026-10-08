-- Prove2me | Theorems.Thm_BSUMM_Det_lemma_2_1
-- name    : BSUMM.Det.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:56.864506+00:00
-- url     : https://prove2.me/theorems/ba2332fd-5465-4fd3-9c4d-1def27d0e955
-- title:
--   Lemma 2.1, constancy clause corrected — Ex and Ax constant on X(y), ∇d(y) = q − Ex(y), ∇d is 1/ρ-Lipschitz on {d ≥ η}
-- statement:
--   Consider problem (1.1) under Assumption A, with augmented Lagrangian $L$, augmented dual $d(y)=\min_{x\in X}L(x;y)$, solution sets $X(y)=\arg\min_{x\in X}L(x;y)$ and primal optimal value $f^*$. Then:
--
--   1. for every $y\in\mathbb R^m$, both $Ex$ and $Ax$ are constant over $X(y)$;
--   2. $d$ is differentiable everywhere, with
--   $$\nabla d(y)=q-Ex(y)\qquad\text{for any }x(y)\in X(y);$$
--   3. for every scalar $\eta\le f^*$, on the superlevel set $U=\{y\in\mathbb R^m\mid d(y)\ge\eta\}$,
--   $$\|\nabla d(y')-\nabla d(y)\|\le\frac1\rho\,\|y'-y\|\qquad\text{for all }y,y'\in U.$$
--
--   The lemma identifies the dual step of BSUM-M as a gradient ascent step on the smooth concave function $d$, and the quantity $\|E\bar x-q\|$ in the convergence proof as $\|\nabla d\|$.
--
--   **Formalization Note** The printed lemma says that "$Ex$ and $A_kx_k$, $k=1,\dots,K$, are constant over $X(y)$", which is copied from a model with separable $g=\sum_k\ell_k(A_kx_k)$. Under this paper's Assumption A(b), $g(x)=\ell(Ax)+\langle x,b\rangle$, only $Ax$ and $Ex$ are constant: with $K=2$, $n_k=1$, $\ell(t)=t^2$, $A=(1\ 1)$, $b=0$, $h=0$, $E=0$, $q=0$, $X=[-1,1]^2$, $X(y)=\{x_1+x_2=0\}\cap X$ and $A_1x_1=x_1$ varies. The statement here has "$Ax$ constant". $d$ is the minimum over $X$ (see the setting).
-- source:
--   Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, pp. 8–9, Lemma 2.1

import Mathlib
import Definitions.Def_BSUMM_Det_Setting

namespace BSUMM.Det

open scoped InnerProductSpace

/-- Lemma 2.1 (Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, pp. 8–9), with the
constancy clause corrected from "`A_k x_k` constant" to "`Ax` constant" (the printed clause is
copied from a separable model and fails for non-separable `ℓ`): under Assumption A, for every
`y`, both `Ex` and `Ax` are constant over `X(y)`; the augmented dual `d` is differentiable with
`∇d(y) = q − Ex(y)` for any `x(y) ∈ X(y)`; and for every `η ≤ f*`, `∇d` is `1/ρ`-Lipschitz on
`U = {y | d(y) ≥ η}`. -/
theorem lemma_2_1 {K : ℕ} {n : Fin K → ℕ} {m p : ℕ} (D : Data K n m p) (hA : D.AssumptionA) :
    (∀ y, ∀ x₁ ∈ D.Xopt y, ∀ x₂ ∈ D.Xopt y, D.Emul x₁ = D.Emul x₂ ∧ D.A x₁ = D.A x₂) ∧
    (∀ y, ∀ xy ∈ D.Xopt y, HasGradientAt D.d (D.q - D.Emul xy) y) ∧
    (∀ η : ℝ, η ≤ D.fstar → ∀ y y' : EuclideanSpace ℝ (Fin m), η ≤ D.d y → η ≤ D.d y' →
      ‖gradient D.d y' - gradient D.d y‖ ≤ 1 / D.ρ * ‖y' - y‖) := by sorry

end BSUMM.Det
