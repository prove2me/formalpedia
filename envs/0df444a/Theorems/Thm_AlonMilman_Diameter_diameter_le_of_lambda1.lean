-- Prove2me | Theorems.Thm_AlonMilman_Diameter_diameter_le_of_lambda1
-- name    : AlonMilman.Diameter.diameter_le_of_lambda1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:29:07.349858+00:00
-- url     : https://prove2.me/theorems/6a30b9a9-ab9a-41f8-b28d-75d1a494ef67
-- title:
--   Theorem 2.7 — $\operatorname{diam} G \le 2\lfloor\sqrt{2d/\lambda_1}\,\log_2 n\rfloor$
-- statement:
--   Let $G = (V, E)$ be a connected finite simple graph on $|V| = n > 1$ vertices, with maximum degree $d$, and put $\lambda = \lambda_1(G)$, the second-smallest eigenvalue of the Laplacian $Q = \operatorname{diag}(d(v)) - A_G$. Then the diameter of $G$ is at most
--   $$
--   2\Big\lfloor \sqrt{\tfrac{2d}{\lambda}}\;\log_2 n \Big\rfloor ,
--   $$
--   that is, any two vertices $u, v$ are joined by a path with at most this many edges.
--
--   The bound shows that a family of bounded-degree graphs whose algebraic connectivity stays bounded away from $0$ has logarithmic diameter; by the paper's Remark 2.8 this order is best possible.
--
--   **Formalization Note** The diameter is expressed pointwise as $\operatorname{dist}(u, v) \le \cdots$ for all $u, v$, with Mathlib's `SimpleGraph.dist`; the graph is assumed connected, so every distance is a genuine path length. $\lambda_1 > 0$ for connected $G$ (p. 76), so the division $2d/\lambda$ is genuine. $[x]$ is `Nat.floor`, $\log_2$ is `Real.logb 2`.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 79, Theorem 2.7 (proof ends p. 80)

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1

namespace AlonMilman.Diameter

theorem diameter_le_of_lambda1 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (hn : 1 < Fintype.card V) :
    ∀ u v : V, G.dist u v ≤
      2 * ⌊Real.sqrt (2 * (G.maxDegree : ℝ) / lambda1 G) *
        Real.logb 2 (Fintype.card V : ℝ)⌋₊ := by sorry

end AlonMilman.Diameter
