-- Prove2me | Theorems.Thm_AlonMilman_Diameter_theorem_2_6
-- name    : AlonMilman.Diameter.theorem_2_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:28:35.045671+00:00
-- url     : https://prove2.me/theorems/7449faee-b56c-4a99-862d-b7d80bf85599
-- title:
--   Theorem 2.6 — $b \le (1-a)\exp(-\ln(1+2a)\lfloor\sqrt{\lambda_1/2d}\,\rho\rfloor)$
-- statement:
--   Let $G = (V, E)$ be a connected finite simple graph on $n \ge 2$ vertices, with maximum degree $d$ and algebraic connectivity $\lambda_1 = \lambda_1(G)$. Let $A, B \subseteq V$ and let $\rho \ge 1$ be a real number (not necessarily an integer) such that every vertex of $A$ is at graph distance strictly greater than $\rho$ from every vertex of $B$. With $a = |A|/n$ and $b = |B|/n$,
--   $$
--   b \le (1 - a)\exp\!\Big(-\ln(1 + 2a)\,\Big\lfloor \sqrt{\tfrac{\lambda_1}{2d}}\;\rho \Big\rfloor\Big),
--   $$
--   where $\lfloor x \rfloor$ is the integer part of $x \ge 0$.
--
--   This is the concentration property of graphs with large $\lambda_1$: the proportion of vertices far from a set $A$ decays exponentially in the distance, measured in units of $\sqrt{2d/\lambda_1}$. The diameter bound of Theorem 2.7 is a direct application.
--
--   **Formalization Note** The paper's $[x]$ is `Nat.floor` (`⌊x⌋₊`), cast to $\mathbb R$; $\sqrt{\lambda_1/2d}$ is $\sqrt{\lambda_1/(2d)}$. The paper labels this display (2.2), reusing the label of Theorem 2.5. Empty $A$ or $B$ make the inequality hold trivially and are not excluded.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 79, Theorem 2.6, Eq. (2.2)

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1

namespace AlonMilman.Diameter

theorem theorem_2_6 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (A B : Finset V) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hdist : ∀ u ∈ A, ∀ v ∈ B, ρ < (G.dist u v : ℝ)) :
    (B.card : ℝ) / Fintype.card V ≤
      (1 - (A.card : ℝ) / Fintype.card V) *
        Real.exp (-Real.log (1 + 2 * ((A.card : ℝ) / Fintype.card V)) *
          (⌊Real.sqrt (lambda1 G / (2 * (G.maxDegree : ℝ))) * ρ⌋₊ : ℝ)) := by sorry

end AlonMilman.Diameter
