-- Prove2me | Theorems.Thm_AlonMilman_Diameter_remark_2_3
-- name    : AlonMilman.Diameter.remark_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:27:37.248005+00:00
-- url     : https://prove2.me/theorems/c3cf3342-f114-4a90-be87-fb286f9dcac4
-- title:
--   Remark 2.3 — $\lambda_1 \le \frac{n}{n-1}\min_v d(v)$
-- statement:
--   Let $G = (V, E)$ be a connected finite simple graph on $n \ge 2$ vertices, $d(v)$ the degree of $v$, and $\lambda_1 = \lambda_1(G)$ the second-smallest eigenvalue of its Laplacian. Then
--   $$
--   \lambda_1 \le \frac{n}{n-1}\,\min\{d(v) : v \in V\}.
--   $$
--
--   In the proof of Theorem 2.6 this gives $\sqrt{2d/\lambda_1} \ge 1$, where $d$ is the maximum degree; the bound itself goes back to Fiedler.
--
--   **Formalization Note** $\min_v d(v)$ is Mathlib's `SimpleGraph.minDegree`; $n$ and the degree are cast to $\mathbb R$.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 78, Remark 2.3 (first sentence)

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1

namespace AlonMilman.Diameter

theorem remark_2_3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (hn : 2 ≤ Fintype.card V) :
    lambda1 G ≤
      ((Fintype.card V : ℝ) / ((Fintype.card V : ℝ) - 1)) * (G.minDegree : ℝ) := by sorry

end AlonMilman.Diameter
