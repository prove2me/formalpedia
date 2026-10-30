-- Prove2me | Theorems.Thm_APrioriTSP_Sampling_dual_certificate_theorem_3
-- name    : APrioriTSP.Sampling.dual_certificate_theorem_3
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-29T14:10:43.133988+00:00
-- url     : https://prove2.me/theorems/f59ae7a8-3684-44ab-ae0e-2cc5c257fda2
-- title:
--   p. 13 — a feasible solution of (Dual-Sampling-LP) for α = 1.5, σ = 0.663 with σ²/y < 3.1
-- statement:
--   This is the computational certificate behind Theorem 3 of the paper.
--
--   Fix $\alpha = 1.5$ and $\sigma = 0.663$. For an integer $N\ge 1$ and $\beta>0$, (Dual-Sampling-LP) is the linear program in variables $x_{i,j}$ ($1\le i\le j$, $i+j\le N$), $v_{i,j}, w_{i,j}$ ($0\le i\le j\le N$) and $y$:
--
--   $$\max\ \sigma^{-2}y$$
--
--   subject to
--
--   1. $4\beta\, e^{-(i+j-1)\sigma\beta}\, y \le v_{i,j}+w_{i,j}$ for $0\le i\le j\le N$ (18);
--   2. for $0\le k\le N$ (19):
--   $$(\alpha+\delta_1)e^{-(k-1)\sigma\beta}y+\sum_{j=k}^N v_{k,j}+\sum_{j=0}^k w_{j,k}+\mathbb 1_{k=1}\,\delta_2 y+\mathbb 1_{k>0}\Big(\sum_{i=1}^{\min\{k,N-k\}}x_{i,k}+\sum_{i=k}^{N-k}x_{k,i}-\sum_{\substack{1\le i\le j\le N\\ i+j=k}}x_{i,j}\Big)\le e^{-(k+\frac12)\beta};$$
--   3. $x,y,v,w\ge 0$ (20),
--
--   where $\delta_1 = \frac{4\beta}{e^{N\sigma\beta}(e^{\sigma\beta}-1)}$ and $\delta_2 = \big(\alpha+\frac{2\beta}{e^{N\sigma\beta}(e^{\sigma\beta}-1)}\big)\frac{e^{-N\sigma\beta}}{(1-e^{-\sigma\beta})^2}(1+N-e^{-\sigma\beta}N)$ are the constants of Lemma 14.
--
--   **Claim.** There exist $\beta>0$, $N\ge 1$ and a feasible solution $(x,y,v,w)$ of (Dual-Sampling-LP) with $y>0$ and
--   $$\frac{\sigma^2}{y} < 3.1 .$$
--
--   The paper reports such a solution, computed with Gurobi 10.0.1 for $\beta = 1/100$ and $N = 2500$, with $\sigma^2/y \le 3.094$ (the solution and a Python verification script are at https://doi.org/10.60507/FK2/JCUIRI). Together with Corollary 16 (any feasible dual solution certifies the bound $\sigma^2/y$ on (2)), it yields Theorem 3.
--
--   **Formalization Note** Feasibility is the platform predicate `DualSamplingLPFeasible 1.5 0.663 β N x y v w` from `Definitions.Def_APrioriTSP_Sampling_LP`, the same one used in `APrioriTSP.Sampling.corollary_16`. The values of $\beta$ and $N$ are quantified existentially (rather than fixed to the paper's $1/100$ and $2500$) so that any valid certificate, possibly a smaller or structured one, proves the claim.
-- source:
--   Blauth, Neuwohner, Puhlmann & Vygen, Improved guarantees for the a priori TSP, arXiv:2309.10663v1, p. 13 (paragraph after Corollary 16: computed dual solution with α = 1.5, β = 1/100, N = 2500, σ = 0.663, upper bound 3.094); (Dual-Sampling-LP) p. 13, constraints (18)–(20)

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting
import Definitions.Def_APrioriTSP_Sampling_LP

namespace APrioriTSP.Sampling

/-- The computed dual solution of p. 13: for `α = 1.5`, `σ = 0.663` there are `β > 0`, `N ≥ 1`
and a feasible solution `(x, y, v, w)` of (Dual-Sampling-LP) with `y > 0` and `σ²/y < 3.1`
(the paper's certificate has `β = 1/100`, `N = 2500`, `σ²/y ≤ 3.094`). -/
theorem dual_certificate_theorem_3 : ∃ (β : ℝ) (N : ℕ) (x : ℕ → ℕ → ℝ) (y : ℝ) (v w : ℕ → ℕ → ℝ),
    0 < β ∧ 1 ≤ N ∧ DualSamplingLPFeasible 1.5 0.663 β N x y v w ∧ 0 < y ∧
      (0.663 : ℝ) ^ 2 / y < 3.1 := by sorry

end APrioriTSP.Sampling
