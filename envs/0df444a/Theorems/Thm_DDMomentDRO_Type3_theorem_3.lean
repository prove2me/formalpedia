-- Prove2me | Theorems.Thm_DDMomentDRO_Type3_theorem_3
-- name    : DDMomentDRO.Type3.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:45:56.214978+00:00
-- url     : https://prove2.me/theorems/2bbb042e-0080-4a33-83f3-9af13cebcde2
-- title:
--   Theorem 3, p. 12 — under Slater, the Type 3 stage Bellman equation (2) equals the mixed-integer SDP (15)
-- statement:
--   Consider one stage $t$ of the Bellman equations (2) with stage feasible set $S$ (binary states), stage cost $g$, finite support $\xi^1,\dots,\xi^K \in \mathbb R^J$, next-stage values $Q^k(x)$, and the Type 3 ambiguity set
--   $$\mathcal P^{D_3}(x) = \Big\{p \ge 0 : \sum_k p_k = 1,\ (\bar\xi(p)-\mu(x))^\top\Sigma(x)^{-1}(\bar\xi(p)-\mu(x)) \le \gamma,\ \sum_k p_k(\xi^k-\mu(x))(\xi^k-\mu(x))^\top \preceq \eta\Sigma(x)\Big\},$$
--   where $\bar\xi(p) = \sum_k p_k\xi^k$. Assume that for every feasible $(x,y) \in S$, $\Sigma(x) \succ 0$ and Slater's condition holds at $x$: some probability vector $p$ satisfies the second constraint with $<$ and the third with $\prec$.
--
--   Then for every real $q$, $q$ is the minimum of the stage Bellman equation
--   $$Q_t = \min_{(x,y)\in S}\Big\{g(x,y) + \max_{p\in\mathcal P^{D_3}(x)} \sum_k p_k Q^k(x)\Big\}$$
--   if and only if $q$ is the minimum of the mixed-integer SDP
--   $$\begin{aligned}\min_{x,y,s,Z,Y}\ & g(x,y) + s + \Sigma(x)\bullet z_1 - 2\mu(x)^\top z_2 + \gamma z_3 + \eta\,\Sigma(x)\bullet Y\\ \text{s.t. }\ & s - 2z_2^\top\xi^k + (\xi^k-\mu(x))(\xi^k-\mu(x))^\top\bullet Y \ge Q^k(x),\ \forall k,\\ & Z = \begin{pmatrix} z_1 & z_2\\ z_2^\top & z_3\end{pmatrix}\succeq 0,\ Y \succeq 0,\ (x,y)\in S.\end{aligned}$$
--
--   This is the paper's main reformulation: under the Delage–Ye-type moment set, the min–max stage problem becomes a single minimization, which is what makes the SDDiP-type algorithms of the paper applicable.
--
--   **Formalization Note** "$q$ is the minimum" is `IsLeast` on the set of values (for the Bellman side, only $(x,y)$ at which the inner maximum is attained contribute, via `IsGreatest`). The statement holds for any $S$ and any $g$: the page's linearity of $g$ and compactness and polyhedrality of $S$ are not needed and are dropped (a disclosed generalization); the binary condition is kept as `hbin`. Added relative to the page: $\Sigma(x) \succ 0$ (implicit, since the page writes $\Sigma(x)^{-1}$), $p \ge 0$ in the ambiguity set ((C-20f)), and the Slater point is a probability vector (Theorem A.3). The Slater clause of the page is cut at the right margin; its missing text is restored from Theorem B.6, p. 36. $\mu,\Sigma$ are arbitrary functions of $x$, and $Q^k$ is a free real function.
-- source:
--   Yu & Shen, Multistage distributionally robust mixed-integer programming with decision-dependent moment-based ambiguity sets, arXiv:2002.12518v3, p. 12, Theorem 3, (14), (15); p. 6, (2); p. 36, Theorem B.6 (Slater text)

import Mathlib
import Definitions.Def_DDMomentDRO_Type3_Setting

namespace DDMomentDRO.Type3

open Matrix

theorem theorem_3 {I J K : ℕ} (S : Set ((Fin I → ℝ) × (Fin I → Fin J → ℝ)))
    (g : (Fin I → ℝ) → (Fin I → Fin J → ℝ) → ℝ) (ξ : Fin K → Fin J → ℝ)
    (Qn : (Fin I → ℝ) → Fin K → ℝ) (μ : (Fin I → ℝ) → Fin J → ℝ)
    (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ) (γ η : ℝ)
    (hbin : ∀ p ∈ S, ∀ i, p.1 i = 0 ∨ p.1 i = 1)
    (hSig : ∀ x y, (x, y) ∈ S → (Sig x).PosDef)
    (hslater : ∀ x y, (x, y) ∈ S → ∃ p : Fin K → ℝ, IsSlaterPoint ξ μ Sig γ η x p) :
    ∀ q : ℝ, IsLeast (stageVals S g Qn ξ μ Sig γ η) q ↔
      IsLeast (dualVals3 S g Qn ξ μ Sig γ η) q := by sorry

end DDMomentDRO.Type3
