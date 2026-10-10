-- Prove2me | Theorems.Thm_DDMomentDRO_Type1_theorem_1
-- name    : DDMomentDRO.Type1.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:45:16.098268+00:00
-- url     : https://prove2.me/theorems/1f31d43a-e9d2-48ae-b659-a8c215ee3040
-- title:
--   Theorem 1, p. 8 — under moment bounds, the stage Bellman equation (2) equals the joint LP-dual minimization (4)
-- statement:
--   Consider one stage $t$ of the multistage decision-dependent distributionally robust model of Yu and Shen. The stage feasible set $S=X_t(x_{t-1},\xi_t)$ consists of pairs $(x,y)$ with binary state $x\in\{0,1\}^I$, $g(x,y)$ is the stage cost, the next-stage support is $\{\xi^1,\dots,\xi^K\}$, $Q_{t+1}(x,\xi^k)$ are the next-stage values, and $\mathcal P^{D_1}(x)$ is the Type 1 ambiguity set (3) of probability vectors with bounds $\underline p(x)\le p\le\bar p(x)$ and moment bounds $l(x)\le\sum_kp_kf(\xi^k)\le u(x)$.
--
--   Suppose $\mathcal P^{D_1}(x)$ is nonempty for every feasible $x$, i.e. every $x$ with $(x,y)\in S$ for some $y$. Then, for every real $q$, the Bellman equation
--   $$Q_t(x_{t-1},\xi_t)=\min_{(x,y)\in S}\Big\{g(x,y)+\max_{p\in\mathcal P^{D_1}(x)}\sum_{k=1}^Kp_kQ_{t+1}(x,\xi^k)\Big\}\tag{2}$$
--   has (attained) optimal value $q$ if and only if the joint program
--   $$\begin{aligned}\min_{\alpha,\beta,\underline\gamma,\bar\gamma,x,y}\ \ & g(x,y)-\alpha^{\mathsf T}l(x)+\beta^{\mathsf T}u(x)-\underline\gamma^{\mathsf T}\underline p(x)+\bar\gamma^{\mathsf T}\bar p(x) &(4a)\\ \text{s.t.}\ \ &(-\alpha+\beta)^{\mathsf T}f(\xi^k)-\underline\gamma_k+\bar\gamma_k\ge Q_{t+1}(x,\xi^k),\ \ \forall k\in[K], &(4b)\\ &(x,y)\in S, &(4c)\\ &\alpha,\beta,\underline\gamma,\bar\gamma\ge0 &(4d)\end{aligned}$$
--   has (attained) optimal value $q$.
--
--   The theorem replaces the min–max Bellman equation by a single minimization, which the paper then linearizes with McCormick envelopes and solves by SDDiP.
--
--   **Formalization Note** "Min" and "max" are encoded as `IsLeast` / `IsGreatest` of the value sets, so both include attainment, and the theorem is the equivalence of the two optimal values for every $q$. The ambiguity set includes $p\ge0$ (the proof's (C-17f), and Assumption 3), which (3) as printed omits; without it the dual constraint (4b) would have to be an equality. The theorem is stated for an arbitrary set $S$ and an arbitrary cost $g$: the page's linearity of $g$ and the compactness and polyhedrality of $S$ are dropped (a disclosed generalisation; the proof does not use them), while the binary state is kept as a hypothesis. $Q_{t+1}$ is an arbitrary real function of $(x,k)$.
-- source:
--   Yu & Shen, Multistage distributionally robust mixed-integer programming with decision-dependent moment-based ambiguity sets, arXiv:2002.12518v3, p. 8, Theorem 1

import Mathlib
import Definitions.Def_DDMomentDRO_Type1_Setting

namespace DDMomentDRO.Type1

/-- Theorem 1 (p. 8): if the Type 1 ambiguity set (3) is nonempty at every feasible state, the
stage Bellman equation (2) has optimal value `q` (attained) if and only if the joint
minimization (4) has optimal value `q` (attained). -/
theorem theorem_1 {I J K m : ℕ}
    (S : Set ((Fin I → ℝ) × (Fin I → Fin J → ℝ)))
    (g : (Fin I → ℝ) → (Fin I → Fin J → ℝ) → ℝ)
    (hbin : ∀ p ∈ S, ∀ i, p.1 i = 0 ∨ p.1 i = 1)
    (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ) (e : Fin m → Fin J → ℕ)
    (l u : (Fin I → ℝ) → Fin m → ℝ) (pl pu : (Fin I → ℝ) → Fin K → ℝ)
    (hne : ∀ x y, (x, y) ∈ S → (amb1 ξ e l u pl pu x).Nonempty) :
    ∀ q : ℝ, IsLeast (stageVals S g (amb1 ξ e l u pl pu) Qn) q ↔
      IsLeast (dualVals1 S g Qn ξ e l u pl pu) q := by sorry

end DDMomentDRO.Type1
