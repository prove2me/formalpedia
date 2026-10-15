-- Prove2me | Theorems.Thm_DynReinsDiv_HJB_eq_A_13
-- name    : DynReinsDiv.HJB.eq_A_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:34:32.94347+00:00
-- url     : https://prove2.me/theorems/88898d38-4cf9-4185-81ec-dc0d17bee35f
-- title:
--   (A.12)–(A.13) — f is continuous with f′ = −A < 0, f(0+) = μ₁ − γ > 0, f(+∞) = −γ, and f has a unique root λ > 0
-- statement:
--   Let $f(y)=-yA(y)+B(y)-\gamma$ be the function (A.12) of a model with tail assumption (3.3) and $0<\gamma<\mu_1$. Then $f$ is continuous, and at **every** $y\in\mathbb R$ it is differentiable with
--   $$f'(y)=-A(y)<0 .$$
--   Hence $f$ is strictly decreasing. Moreover
--   $$\lim_{y\to0+}f(y)=\mu_1-\gamma>0,\qquad \lim_{y\to+\infty}f(y)=-\gamma<0,$$
--   and $f$ has exactly one root, which is positive. This root is the constant $\lambda$ used throughout the paper.
--
--   The constant $\lambda$ enters the boundary condition $(\lambda v_x+v_{xx})(0,t)=0$ of the gradient problem, the bound (3.9) of Theorem 3.1 and every lemma on the penalized problem.
--
--   **Formalization Note** The derivative formula holds everywhere, including at points $y$ where $F$ jumps at $1/y$: there $A$ and $B$ have a corner but $-yA+B$ does not. The paper's $f$ is `fA`.
-- source:
--   Guan, Xu & Zhou, Dynamic optimal reinsurance and dividend-payout in a finite time horizon, arXiv:2008.00391v3, p. 23, (A.12)–(A.13) and the definition of λ

import Mathlib
import Definitions.Def_DynReinsDiv_HJB_Model

namespace DynReinsDiv.HJB

theorem eq_A_13 (M : Model) :
    Continuous M.fA ∧
    (∀ y : ℝ, HasDerivAt M.fA (-M.A y) y ∧ -M.A y < 0) ∧
    StrictAnti M.fA ∧
    Filter.Tendsto M.fA (nhdsWithin 0 (Set.Ioi 0)) (nhds (M.μ₁ - M.γ)) ∧ 0 < M.μ₁ - M.γ ∧
    Filter.Tendsto M.fA Filter.atTop (nhds (-M.γ)) ∧ -M.γ < 0 ∧
    (∃! lam : ℝ, M.fA lam = 0) ∧
    ∀ lam : ℝ, M.fA lam = 0 → 0 < lam := by sorry

end DynReinsDiv.HJB
