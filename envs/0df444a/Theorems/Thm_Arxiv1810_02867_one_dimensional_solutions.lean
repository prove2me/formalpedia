-- Prove2me | Theorems.Thm_Arxiv1810_02867_one_dimensional_solutions
-- name    : Arxiv1810_02867.one_dimensional_solutions
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T05:21:32.709246+00:00
-- url     : https://prove2.me/theorems/f6b4804f-2682-44e4-87d0-7e8848e2aaad
-- title:
--   Eqs. (5)-(6): one-way solutions of the 1D non-reciprocal wave equation
-- statement:
--   Let $\alpha,\beta>0$, let $c=(\alpha\beta)^{-1/2}$, and let $\gamma\in\mathbb R$ satisfy the standing assumption $|\gamma|<1/c$. Let $S$ be twice continuously differentiable. Then
--   $$P^\pm(x_1,t)=S\Big(t\mp\frac{x_1}{c}(1\pm\gamma c)\Big)$$
--   both solve the one-dimensional homogeneous source-free equation (5):
--   $$(\partial_1+\gamma\partial_t)(\partial_1+\gamma\partial_t)P-\alpha\beta\,\partial_t^2P=0.$$
--   Moreover $P^+(x_1,t)=S\big(t-\frac{1+\gamma c}{c}x_1\big)$ and $P^-(x_1,t)=S\big(t-\frac{1-\gamma c}{c}(-x_1)\big)$, with slownesses $\frac{1+\gamma c}{c}>0$ and $\frac{1-\gamma c}{c}>0$. So $P^+$ propagates in the positive and $P^-$ in the negative $x_1$-direction.
--
--   **Formalization Note** The paper writes "Its solution reads". The statement records that both one-way waves are solutions; it does not assert that every solution is a superposition of them.
-- source:
--   Wapenaar and Reinicke, Unified wave field retrieval and imaging method for inhomogeneous non-reciprocal media, arXiv:1810.02867v2 (2020), claim c002; Section II, eqs. (5)-(6) and the standing assumption on |gamma_r|, PDF p. 4

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

open MeasureTheory Matrix

namespace Arxiv1810_02867

theorem one_dimensional_solutions (alpha beta gamma : ℝ) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hgamma : |gamma| < 1 / refVel alpha beta) (S : ℝ → ℝ) (hS : ContDiff ℝ 2 S) :
    (∀ (plus : Bool) (x t : ℝ),
      D1g gamma (D1g gamma (oneWay plus alpha beta gamma S)) x t -
        alpha * beta * deriv (fun s => deriv (fun s' => oneWay plus alpha beta gamma S x s') s) t
        = 0) ∧
    (∀ x t, oneWay true alpha beta gamma S x t =
      S (t - (1 + gamma * refVel alpha beta) / refVel alpha beta * x)) ∧
    (∀ x t, oneWay false alpha beta gamma S x t =
      S (t - (1 - gamma * refVel alpha beta) / refVel alpha beta * (-x))) ∧
    0 < (1 + gamma * refVel alpha beta) / refVel alpha beta ∧
    0 < (1 - gamma * refVel alpha beta) / refVel alpha beta := by sorry

end Arxiv1810_02867
