-- Prove2me | Theorems.Thm_BHTOpinion_Approx_theorem7_finite_horizon_approximation
-- name    : BHTOpinion.Approx.theorem7_finite_horizon_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:57.759984+00:00
-- url     : https://prove2.me/theorems/05007ad6-61e8-4358-8659-f82ba71254e1
-- title:
--   Theorem 7 — the n-agent model approximates the continuum model uniformly on every [0, T] (discrete time rescaled by 1/n)
-- statement:
--   Let $\tilde x_0$ be a regular initial opinion function, $\tilde x_0\in X_m^M$ for some $m,M>0$, and let $x$ be a solution of the continuum model (3.2) with initial condition $\tilde x_0$. For every $n\ge1$ let $\xi^{\langle n\rangle}:[0,\infty)\to\mathbb R^n$ be a solution of the discrete-agent model (2.1) such that
--
--   1. $\xi^{\langle n\rangle}(0)$ is nondecreasing ($j>i\Rightarrow\xi^{\langle n\rangle}_j(0)\ge\xi^{\langle n\rangle}_i(0)$);
--   2. $\xi^{\langle n\rangle}(0)$ is a proper initial condition and $\xi^{\langle n\rangle}$ is its unique solution;
--   3. $\lim_{n\to\infty}\|G(\xi^{\langle n\rangle}(0))-\tilde x_0\|_\infty=0$.
--
--   Then for every $T$ and every $\varepsilon>0$ there exists $n'$ such that
--
--   $$\bigl\|G\bigl(\xi^{\langle n\rangle}(t/n)\bigr)-x_t\bigr\|_\infty\le\varepsilon\qquad\text{for all }t\in[0,T]\text{ and }n\ge n'.$$
--
--   The continuum model is thus the limit of the $n$-agent model as $n\to\infty$, uniformly on every finite time interval. The approximation is not claimed on $[0,\infty)$: whether the limits of the two models are close is open, and is the gap between the continuum result on intercluster distances and the paper's Conjecture 1 for finitely many agents.
--
--   **Formalization Note** The page writes $G(\xi^{\langle n\rangle}(t))$. As printed the theorem is false: with $\tilde x_0(\alpha)=\alpha/2$ and $\xi^{\langle n\rangle}_i(0)=\tilde x_0(i/n)$ all opinions stay within $1/2$ of each other, the continuum solution is $x_t(\alpha)=\bar x+(\alpha/2-\bar x)e^{-t}$ while the $n$-agent solution relaxes at rate $e^{-nt}$, and at $t=1$ the sup distance tends to $e^{-1}/4$. The cause is the factor $1/n$ between $\mathcal L(G(\xi))$ and the right-hand side of (2.1); the Lean statement rescales the discrete time to $t/n$ (equivalently, the theorem holds for the weighted model (2.4) with weights $1/n$; only the rescaled form is formalized). The sequence is indexed by $n\in\mathbb N$ and every hypothesis and the conclusion are imposed only for $n\ge1$. The limit in 3 is written as: for every $\delta>0$ there is $N$ with $|G(\xi^{\langle n\rangle}(0))(\alpha)-\tilde x_0(\alpha)|\le\delta$ for all $n\ge N$, $n\ge1$ and $\alpha\in I$; the sup norm in the conclusion is likewise pointwise over $I=[0,1]$. "The solution $x_t$" is read as any solution of (3.2) from $\tilde x_0$ (Theorem 4 gives uniqueness).
-- source:
--   Blondel, Hendrickx, Tsitsiklis, Continuous-time average-preserving opinion dynamics with opinion-dependent communications, SIAM J. Control Optim. 48 (2010), Theorem 7, p. 5232 (discrete time rescaled; see note)

import Mathlib
import Definitions.Def_BHTOpinion_Approx_Discrete
import Definitions.Def_BHTOpinion_Approx_Continuum

namespace BHTOpinion.Approx

theorem theorem7_finite_horizon_approximation (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (x0 : ℝ → ℝ) (hx0m : BHTOpinion.Continuum.InXm m x0) (hx0M : BHTOpinion.Continuum.InXM M x0)
    (x : ℝ → ℝ → ℝ) (hx : BHTOpinion.Continuum.IsSolution x0 x)
    (ξ : (n : ℕ) → ℝ → Fin n → ℝ)
    (hproper : ∀ n : ℕ, 0 < n → IsProperDiscreteSolution (ξ n))
    (hsorted : ∀ n : ℕ, 0 < n → Monotone (ξ n 0))
    (hinit : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
      ∀ α ∈ BHTOpinion.Continuum.I, |G (ξ n 0) α - x0 α| ≤ δ) :
    ∀ T ε : ℝ, 0 < ε → ∃ n' : ℕ, ∀ n : ℕ, n' ≤ n → 0 < n →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α ∈ BHTOpinion.Continuum.I, |G (ξ n (t / n)) α - x t α| ≤ ε := by sorry

end BHTOpinion.Approx
