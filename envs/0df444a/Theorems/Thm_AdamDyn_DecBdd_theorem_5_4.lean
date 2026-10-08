-- Prove2me | Theorems.Thm_AdamDyn_DecBdd_theorem_5_4
-- name    : AdamDyn.DecBdd.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:27.972527+00:00
-- url     : https://prove2.me/theorems/49655b32-5e76-4f57-b257-5f10b5a58b38
-- title:
--   Theorem 5.4 — decreasing-step Adam iterates are almost surely bounded
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $(\Xi,\mathfrak S)$ a measurable space with a probability measure $\mu$, $f:\mathbb R^d\times\Xi\to\mathbb R$ with gradient $\nabla f(x,\xi)$ in $x$, and $F(x)=\mathbb E f(x,\xi)$. Assume:
--
--   1. Assumption 2.2 (regularity and local $L^2$-Lipschitz gradients of $f$);
--   2. Assumption 2.3: $F$ is coercive, $F(x)\to+\infty$ as $\|x\|\to\infty$;
--   3. Assumption 4.1: $(\xi_n)_{n\ge1}$ is iid with law $\mu$;
--   4. Assumption 5.1 (stepsizes $\gamma_n$ and moment parameters $\alpha_n,\beta_n$, with $0<b<4a$);
--   5. Assumption 5.3 ($\nabla F$ Lipschitz, $\mathbb E\|\nabla f(x,\xi)\|^2\le C(1+F(x))$, and the limsup condition);
--   6. Assumption 4.2 i) with $p=4$: $\sup_{x\in K}\mathbb E\|\nabla f(x,\xi)\|^4<\infty$ for every compact $K$.
--
--   Let $\varepsilon>0$, $\alpha_1<1$, $\beta_1<1$, and let $((x_n,m_n,v_n):n\in\mathbb N)$ be the random sequence given by Algorithm 5.1 from $(x_0,0,0)$. Then, with probability one,
--   $$\sup_{n\in\mathbb N}\big\|(x_n,m_n,v_n)\big\|<\infty .$$
--
--   Theorem 5.2 of the paper proves almost sure convergence of decreasing-step Adam to the critical points of $F$ under the assumption that the iterates are a.s. bounded; Theorem 5.4 supplies that assumption from conditions on $f$ and the stepsizes alone.
--
--   **Formalization Note** The conclusion is `∀ᵐ ω ∂P, Bornology.IsBounded (Set.range fun n => (x_n, m_n, v_n)(ω))`: one bound for the whole trajectory, not finiteness of each iterate. $E\times E\times E$ carries Mathlib's product norm (the max of the three Euclidean norms), which defines the same bounded sets as the Euclidean norm of $\mathbb R^{3d}$. $\varepsilon>0$ is implicit on the page (Adam divides by $\varepsilon+\sqrt{\hat v_n}$), and $\alpha_1<1$, $\beta_1<1$ are implicit in Algorithm 5.1, which divides by $r_1=1-\alpha_1$ and $\bar r_1=1-\beta_1$ (Assumption 5.1 iii) alone allows $\alpha_1=1$). No projection step and no almost-sure bound on $\nabla f(x,\xi)$ are assumed. The gradient $\nabla f(\cdot,\xi)$ is a fixed function `gf` agreeing with the true gradient for $\mu$-a.e. $\xi$; since each $\xi_n$ has law $\mu$, the iterates are determined up to a null event.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 8, Theorem 5.4 (proof: §9.2, pp. 26–27)

import Mathlib
import Definitions.Def_AdamDyn_DecBdd_Algorithm
import Definitions.Def_AdamDyn_DecBdd_Assumptions

open MeasureTheory Filter Topology

namespace AdamDyn.DecBdd

/-- Theorem 5.4 (p. 8). Under Assumptions 2.2, 2.3, 4.1, 5.1, 5.3 and 4.2 i) with `p = 4`, the
sequence `((x_n, m_n, v_n) : n ∈ ℕ)` given by Algorithm 5.1 is bounded with probability one. -/
theorem theorem_5_4 {d : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : AdamDyn.ConstStep.E d → Ξ → ℝ) (gf : AdamDyn.ConstStep.E d → Ξ → AdamDyn.ConstStep.E d) (ξ : ℕ → Ω → Ξ)
    (γ α β : ℕ → ℝ) (a b ε : ℝ) (x0 : AdamDyn.ConstStep.E d)
    (hε : 0 < ε)
    (h22 : Assumption22 f gf μ)
    (h23 : Tendsto (objective f μ) (cocompact (AdamDyn.ConstStep.E d)) atTop)
    (h41 : AdamDyn.DecConv.Assumption41 P μ ξ)
    (h51 : AdamDyn.DecConv.Assumption51 γ α β a b)
    (h53 : Assumption53 f gf μ γ α a b)
    (h42 : Assumption42i gf μ 4)
    (hα1 : α 1 < 1) (hβ1 : β 1 < 1) :
    ∀ᵐ ω ∂P, Bornology.IsBounded (Set.range fun n => adamIter gf γ α β ε x0 ξ n ω) := by sorry

end AdamDyn.DecBdd
