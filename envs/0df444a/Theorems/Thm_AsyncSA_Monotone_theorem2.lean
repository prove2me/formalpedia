-- Prove2me | Theorems.Thm_AsyncSA_Monotone_theorem2
-- name    : AsyncSA.Monotone.theorem2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:01.210844+00:00
-- url     : https://prove2.me/theorems/f60b3943-920c-4e51-bfaf-5ac3d97f2384
-- title:
--   Theorem 2 — under Assumptions 1–4, bounded asynchronous stochastic approximation iterates converge to x* w.p.1
-- statement:
--   Consider the asynchronous stochastic approximation algorithm on $\mathbb R^n$,
--   $$
--   x_i(t+1)=x_i(t)+\alpha_i(t)\bigl(F_i(x^i(t))-x_i(t)+w_i(t)\bigr),\qquad x^i(t)=\bigl(x_1(\tau^i_1(t)),\dots,x_n(\tau^i_n(t))\bigr),
--   $$
--   with stepsizes $\alpha_i(t)\in[0,1]$, noise $w_i(t)$ and delays $0\le\tau^i_j(t)\le t$, all random variables on a probability space $(\Omega,\mathcal F,P)$ with an increasing sequence of σ-fields $\{\mathcal F(t)\}$. Suppose
--
--   1. *Assumption 1*: $\tau^i_j(t)\to\infty$ w.p.1 for all $i,j$;
--   2. *Assumption 2*: $x(0)$ is $\mathcal F(0)$-measurable, $w_i(t)$ is $\mathcal F(t+1)$-measurable, $\alpha_i(t),\tau^i_j(t)$ are $\mathcal F(t)$-measurable, $E[w_i(t)\mid\mathcal F(t)]=0$, and $E[w_i^2(t)\mid\mathcal F(t)]\le A+B\max_j\max_{\tau\le t}|x_j(\tau)|^2$ for deterministic $A,B$;
--   3. *Assumption 3*: $\sum_t\alpha_i(t)=\infty$ w.p.1 and $\sum_t\alpha_i^2(t)\le C$ w.p.1 for a deterministic $C$;
--   4. *Assumption 4*: $F$ is monotone (componentwise), continuous, has the unique fixed point $x^*$, and $F(x)-re\le F(x-re)\le F(x+re)\le F(x)+re$ for every $x$ and every $r>0$ ($e$ the vector of ones).
--
--   Suppose moreover that $x(t)$ is bounded with probability 1. Then
--   $$
--   \lim_{t\to\infty}x(t)=x^*\qquad\text{with probability 1.}
--   $$
--
--   The theorem covers, for instance, Q-learning for undiscounted (stochastic shortest path) problems, where the relevant Bellman operator is monotone but not a contraction; boundedness of the iterates must then be established separately.
--
--   **Formalization Note** The conditional expectations are generalized (set-integral) conditional expectations, not Mathlib's `condExp`; series conditions are stated through partial sums; the update holds in the paper's unified form for every $t$ (no explicit update sets $T^i$). The paper treats $x(t)$ as a random variable determined by the history $\mathcal F(t)$ and uses this implicitly; the statement assumes it explicitly (`Adapted`). The bound in "$x(t)$ is bounded with probability 1" may depend on the sample path. $x^*$ is the same vector as the fixed point in Assumption 4. Convergence is in $\mathbb R^n$ (product topology, equivalently the maximum norm). Components are indexed by `Fin n` (0-based).
-- source:
--   Tsitsiklis, Asynchronous Stochastic Approximation and Q-Learning, Machine Learning 16 (1994), p. 189, Theorem 2

import Mathlib
import Definitions.Def_AsyncSA_Monotone_Model

namespace AsyncSA.Monotone

open MeasureTheory Filter Topology

theorem theorem2 {n : ℕ} {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℕ m0) (alg : Algorithm n Ω) (xstar : Fin n → ℝ)
    (h1 : alg.Assumption1 P) (h2 : alg.Assumption2 P 𝓕) (hx : alg.Adapted 𝓕)
    (h3 : alg.Assumption3 P) (h4 : Assumption4 alg.F xstar)
    (hbdd : ∀ᵐ ω ∂P, ∃ M : ℝ, ∀ t j, |alg.x t ω j| ≤ M) :
    ∀ᵐ ω ∂P, Tendsto (fun t => alg.x t ω) atTop (𝓝 xstar) := by sorry

end AsyncSA.Monotone
