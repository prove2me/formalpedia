-- Prove2me | Theorems.Thm_DDMomentDRO_Type2_theorem_2
-- name    : DDMomentDRO.Type2.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:45:13.875973+00:00
-- url     : https://prove2.me/theorems/5a300bb3-ad7e-403b-9ea5-a7309ee40332
-- title:
--   Theorem 2, p. 11 — with nonempty Type 2 ambiguity sets, the stage Bellman equation (2) equals the single minimization (11)
-- statement:
--   Consider one stage $t$ of the Bellman equations (2) under the Type 2 ambiguity set (10): a stage feasible set $S=X_t(x_{t-1},\xi_t)$ of pairs $(x_t,y_t)$ with binary state $x_t\in\{0,1\}^I$, a stage cost $g_t$, a finite support $\{\xi^k_{t+1}\}_{k=1}^K\subset\mathbb R^J$, next-stage values $Q^k_{t+1}(x_t)$, and a decision-dependent mean $\mu(x_t)$ and covariance $\Sigma(x_t)$. Suppose that for every feasible $x_t$ (every $x_t$ with some $y_t$ such that $(x_t,y_t)\in S$) the ambiguity set $\mathcal P^{D_2}_{t+1}(x_t)$ is nonempty. Then for every real $q$,
--   $$
--   q=\min_{(x_t,y_t)\in S}\Big\{g_t(x_t,y_t)+\max_{p\in\mathcal P^{D_2}_{t+1}(x_t)}\sum_{k=1}^Kp_kQ^k_{t+1}(x_t)\Big\}
--   $$
--   holds (with both the minimum and the inner maxima attained) if and only if $q$ is the attained minimum of
--   $$
--   \begin{aligned}
--   \min_{x_t,y_t,s,u,Y}\ & g_t(x_t,y_t)+s+u^\top\mu(x_t)+\Sigma(x_t)\bullet Y &&\text{(11a)}\\
--   \text{s.t. }\ & s+u^\top\xi^k_{t+1}+(\xi^k_{t+1}-\mu(x_t))(\xi^k_{t+1}-\mu(x_t))^\top\bullet Y\ge Q^k_{t+1}(x_t),\ \ \forall k\in[K], &&\text{(11b)}\\
--   & (x_t,y_t)\in S,
--   \end{aligned}
--   $$
--   where $s\in\mathbb R$, $u\in\mathbb R^J$, $Y\in\mathbb R^{J\times J}$ and $A\bullet B=\operatorname{trace}(A^\top B)$.
--
--   In words: the min–max Bellman equation of stage $t$ can be rewritten as one minimization in which the worst-case expectation is replaced by its LP dual. Under the affine maps (12) and McCormick envelopes for the binary state this becomes the mixed-integer linear program that the paper's SDDiP algorithm solves.
--
--   **Formalization Note** The theorem holds for arbitrary $S$ and $g_t$, so the page's standing assumptions that $g_t$ is linear and $X_t$ is a nonempty compact mixed-integer polyhedron are not imposed (a disclosed generalization); the binary state is kept as the hypothesis `hbin`, which the statement does not need. The next-stage values are an arbitrary function of the state and the scenario. The ambiguity set includes $p\ge0$ ((C-18e) of the proof; (10) as printed omits it). The equality "$Q_t=$ (11)" is stated as: $q$ is the least stage value if and only if $q$ is the least value of (11), so both the existence of the minima and their equality are asserted.
-- source:
--   Yu & Shen, Multistage distributionally robust mixed-integer programming with decision-dependent moment-based ambiguity sets, arXiv:2002.12518v3, p. 11, Theorem 2, (11a)–(11b); setting pp. 5–6, (2), Assumption 3; p. 10, (10)

import Mathlib
import Definitions.Def_DDMomentDRO_Type2_Setting

namespace DDMomentDRO.Type2

theorem theorem_2 {I J K : ℕ}
    (S : Set ((Fin I → ℝ) × (Fin I → Fin J → ℝ)))
    (g : (Fin I → ℝ) → (Fin I → Fin J → ℝ) → ℝ) (Qn : (Fin I → ℝ) → Fin K → ℝ)
    (ξ : Fin K → Fin J → ℝ) (μ : (Fin I → ℝ) → Fin J → ℝ)
    (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ)
    (hbin : ∀ z ∈ S, ∀ i, z.1 i = 0 ∨ z.1 i = 1)
    (hne : ∀ x y, (x, y) ∈ S → (amb2 ξ μ Sig x).Nonempty) :
    ∀ q : ℝ,
      IsLeast (stageVals S g Qn ξ μ Sig) q ↔ IsLeast (dualVals2 S g Qn ξ μ Sig) q := by sorry

end DDMomentDRO.Type2
