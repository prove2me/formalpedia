-- Prove2me | Theorems.Thm_BSUMM_Rand_lemma_2_1
-- name    : BSUMM.Rand.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:00.95099+00:00
-- url     : https://prove2.me/theorems/db0cfe07-9137-4250-b2be-964287641789
-- title:
--   Lemma 2.1 — Ex and Ax constant on X(y); d differentiable with ∇d(y) = q − Ex(y); ∇d is 1/ρ-Lipschitz on {d ≥ η}
-- statement:
--   Assume the standing Assumption A for problem (1.1). Let $L(x;y)$ be the augmented Lagrangian, $d(y)=\min_{x\in X}L(x;y)$ the augmented dual function, $X(y)$ the set of minimizers of $L(\cdot;y)$ over $X$, and $f^*$ the optimal value of (1.1). Then:
--
--   1. for every $y\in\mathbb R^m$ the set $X(y)$ is nonempty, and both $Ex$ and $Ax$ are constant over $X(y)$;
--   2. $d$ is differentiable everywhere, with
--   $$\nabla d(y)=q-Ex(y)\qquad\text{for any } x(y)\in X(y);$$
--   3. for any scalar $\eta\le f^*$, on the level set $U=\{y\mid d(y)\ge\eta\}$,
--   $$\|\nabla d(y')-\nabla d(y)\|\le\frac1\rho\|y'-y\|\qquad\forall\,y',y\in U.$$
--
--   The dual gradient formula turns the dual step of the method into a gradient ascent step on $d$, and the Lipschitz bound controls how fast $\nabla d$ moves between iterates.
--
--   **Formalization Note** The page states that $A_kx_k$ is constant over $X(y)$ for every block $k$. For the non-separable $g(x)=\ell(Ax)+\langle x,b\rangle$ this fails (with $K=2$, $\ell(t)=t^2$, $A=(1\ 1)$, $E=0$, $X=[-1,1]^2$, every $x$ with $x_1+x_2=0$ is in $X(y)$), so the statement asserts that $Ax$ is constant, which is what strict convexity of $\ell$ gives. Nonemptiness of $X(y)$ is implicit on the page ("where $x(y)\in X(y)$") and is stated explicitly.
-- source:
--   Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, pp. 8–9, Lemma 2.1

import Mathlib
import Definitions.Def_BSUMM_Rand_Setting
import Definitions.Def_BSUMM_Rand_RBSUMM

open scoped RealInnerProductSpace

namespace BSUMM.Rand

/-- Lemma 2.1 (arXiv:1401.7079v1, pp. 8–9), with the printed "`A_k x_k` constant over `X(y)`" read
as "`Ax` constant over `X(y)`" (the blockwise claim fails for non-separable `ℓ(Ax)`):
for every `y`, `X(y)` is nonempty and `Ex`, `Ax` are constant over it; `d` is differentiable with
`∇d(y) = q - Ex(y)` for any `x(y) ∈ X(y)`; and for any `η ≤ f*`, `∇d` is `1/ρ`-Lipschitz on
`U = {y | d(y) ≥ η}`. -/
theorem lemma_2_1 (S : Setting) (hA : S.AssumptionA) :
    (∀ y : S.Ysp, (S.Xopt y).Nonempty) ∧
    (∀ y : S.Ysp, ∀ x ∈ S.Xopt y, ∀ x' ∈ S.Xopt y, S.Emap x = S.Emap x' ∧ S.A x = S.A x') ∧
    (∀ y : S.Ysp, ∀ xy ∈ S.Xopt y, HasGradientAt S.d (S.q - S.Emap xy) y) ∧
    (∀ η : ℝ, η ≤ S.fstar → ∀ y' y : S.Ysp, η ≤ S.d y' → η ≤ S.d y →
      ‖gradient S.d y' - gradient S.d y‖ ≤ 1 / S.ρ * ‖y' - y‖) := by sorry

end BSUMM.Rand
