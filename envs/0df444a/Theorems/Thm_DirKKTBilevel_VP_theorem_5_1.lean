-- Prove2me | Theorems.Thm_DirKKTBilevel_VP_theorem_5_1
-- name    : DirKKTBilevel.VP.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:55.862065+00:00
-- url     : https://prove2.me/theorems/31dcaea5-174f-4ad1-9b09-4e149ddb96ee
-- title:
--   Theorem 5.1, p. 22 — under directional calmness of (VP), a local minimizer of a bilevel program satisfies the directional KKT condition
-- statement:
--   Consider the bilevel program
--   $$\text{(BP)}\qquad\min_{x,y}\ F(x,y)\quad\text{s.t.}\quad y\in S(x),\ G(x,y)\le0,$$
--   where $S(x)$ is the solution set of the lower level program $\min_y f(x,y)$ s.t. $g(x,y)\le0$, and $F,f:\mathbb R^n\times\mathbb R^m\to\mathbb R$, $g:\mathbb R^n\times\mathbb R^m\to\mathbb R^p$, $G:\mathbb R^n\times\mathbb R^m\to\mathbb R^q$ are continuously differentiable. Let $V(x)=\inf_y\{f(x,y)\mid g(x,y)\le0\}$ be the value function.
--
--   Let $(\bar x,\bar y)$ be a local minimizer of (BP). Suppose that
--
--   1. $V$ is directionally Lipschitz continuous and directionally differentiable at $\bar x$ in direction $u$;
--   2. $(u,v)\in C(\bar x,\bar y)$, the critical cone of (VP);
--   3. (VP) is calm at $(\bar x,\bar y)$ in direction $(u,v)$.
--
--   Then the directional KKT condition holds: there exist $\lambda_V\in\mathbb R$, $\lambda_g\in\mathbb R^p$, $\lambda_G\in\mathbb R^q$ such that
--   $$0\in\nabla F(\bar x,\bar y)+\lambda_V\nabla f(\bar x,\bar y)+\lambda_V\,\partial(-V)(\bar x;u)\times\{0\}+\nabla g(\bar x,\bar y)^T\lambda_g+\nabla G(\bar x,\bar y)^T\lambda_G,$$
--   $$\lambda_V\ge0,\quad 0\le\lambda_g\perp g(\bar x,\bar y),\quad \lambda_g\perp\nabla g(\bar x,\bar y)(u,v),\quad 0\le\lambda_G\perp G(\bar x,\bar y),\quad \lambda_G\perp\nabla G(\bar x,\bar y)(u,v).$$
--
--   Here $\partial(-V)(\bar x;u)$ is the directional limiting subdifferential of $-V$. The theorem gives a KKT-type necessary condition for bilevel programs under a calmness condition required only in a critical direction, which is weaker than the classical (nondirectional) calmness that the value-function approach otherwise needs.
--
--   **Formalization Note** The inclusion "$0\in\dots$" is stated as the existence of $\xi\in\partial(-V)(\bar x;u)$ making the sum zero. The value function is `EReal`-valued, and "directionally Lipschitz" includes finiteness of $V$ on $\bar x+\mathcal V_{\varepsilon,\delta}(u)$ (Definition 2.4 is written for real-valued maps); directional differentiability is that of the real function $V$ on that neighbourhood, with value $V'(\bar x;u)$, which also enters the critical cone. The pair $(x,y)$ lives in the Euclidean product `WithLp 2 (E n × E m)`; $\nabla g(\bar x,\bar y)^T\lambda_g=\sum_i(\lambda_g)_i\nabla g_i(\bar x,\bar y)$, and each $\perp$ is an inner product (with the sign conditions, equivalent to componentwise complementarity). The paper obtains the result by applying Theorem 3.1 to (VP).
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, p. 22, Theorem 5.1

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional

namespace DirKKTBilevel.VP

/-- Theorem 5.1, p. 22: let `(x̄, ȳ)` be a local minimizer of (BP), let `V` be directionally
Lipschitz continuous and directionally differentiable at `x̄` in direction `u` (with
`V'(x̄; u) = dV`), let `(u, v) ∈ C(x̄, ȳ)`, and let (VP) be calm at `(x̄, ȳ)` in direction `(u, v)`.
Then the directional KKT condition holds: there are `λ_V, λ_g, λ_G` and `ξ ∈ ∂(−V)(x̄; u)` with
`0 = ∇F + λ_V∇f + λ_V(ξ, 0) + ∇gᵀλ_g + ∇Gᵀλ_G` at `(x̄, ȳ)`, `λ_V ≥ 0`,
`0 ≤ λ_g ⊥ g(x̄, ȳ)`, `λ_g ⊥ ∇g(x̄, ȳ)(u, v)`, `0 ≤ λ_G ⊥ G(x̄, ȳ)`, `λ_G ⊥ ∇G(x̄, ȳ)(u, v)`. -/
theorem theorem_5_1 {n m p q : ℕ} (F f : Z n m → ℝ) (g : Z n m → E p) (G : Z n m → E q)
    (hF : ContDiff ℝ 1 F) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hG : ContDiff ℝ 1 G)
    (x : E n) (y : E m) (u : E n) (v : E m) (dV : ℝ)
    (hmin : IsLocalMinBP F f g G x y)
    (hLip : DirLipschitzAtEReal (valueFn f g) x u)
    (hdiff : HasDirDerivAt (fun x' => (valueFn f g x').toReal) x u dV)
    (hcrit : criticalConeVP F f g G x y dV (WithLp.toLp 2 (u, v)))
    (hcalm : IsCalmDirVP F f g G x y (WithLp.toLp 2 (u, v))) :
    ∃ (lV : ℝ) (lg : E p) (lG : E q) (ξ : E n),
      ξ ∈ dirSubdiff (fun x' => -(valueFn f g x')) x u ∧
      gradient F (WithLp.toLp 2 (x, y)) + lV • gradient f (WithLp.toLp 2 (x, y))
          + lV • (WithLp.toLp 2 (ξ, 0) : Z n m)
          + ∑ i, lg i • gradient (fun z => g z i) (WithLp.toLp 2 (x, y))
          + ∑ j, lG j • gradient (fun z => G z j) (WithLp.toLp 2 (x, y)) = 0 ∧
      0 ≤ lV ∧
      (∀ i, 0 ≤ lg i) ∧ ∑ i, lg i * g (WithLp.toLp 2 (x, y)) i = 0 ∧
      ∑ i, lg i * fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, v)) = 0 ∧
      (∀ j, 0 ≤ lG j) ∧ ∑ j, lG j * G (WithLp.toLp 2 (x, y)) j = 0 ∧
      ∑ j, lG j * fderiv ℝ (fun z => G z j) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, v)) = 0 := by sorry

end DirKKTBilevel.VP
