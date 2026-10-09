-- Prove2me | Theorems.Thm_EvenCycleTuran_PathCount_remark_3
-- name    : EvenCycleTuran.PathCount.remark_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:27:41.8018+00:00
-- url     : https://prove2.me/theorems/d595dff9-ca33-4f21-896b-1d5a4cb4e328
-- title:
--   Remark 3 — a graph has at least 2l copies of P_{2l} per copy of C_{2l}
-- statement:
--   Let $l\ge2$ and let $G$ be a finite graph. Write $\mathcal N(H,G)$ for the number of unlabelled copies of $H$ in $G$, $C_{2l}$ for the cycle on $2l$ vertices and $P_{2l}$ for the path on $2l$ vertices. Then
--
--   $$
--   \mathcal N(P_{2l},G)\ \ge\ 2l\cdot\mathcal N(C_{2l},G).
--   $$
--
--   Every copy of $C_{2l}$ contains $2l$ copies of $P_{2l}$ (delete one of its $2l$ edges), and a copy of $P_{2l}$ lies in at most one copy of $C_{2l}$. This inequality transfers upper bounds on path counts to upper bounds on cycle counts; with Theorem 23 it gives the upper half of Theorem 24.
--
--   **Formalization Note** The hypothesis $l\ge2$ is the paper's implicit one: $C_{2l}$ is a cycle only for $2l\ge3$. At $l=1$ Mathlib's `cycleGraph 2` is a single edge, equal to $P_2$, and the inequality would fail for any graph with an edge.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 32, Remark 3

import Mathlib
import Definitions.Def_EvenCycleTuran_PathCount_Setting

namespace EvenCycleTuran.PathCount

/-- Remark 3: a graph has at least `2l` times as many copies of `P_{2l}` as of `C_{2l}`. -/
theorem remark_3 (l : ℕ) (hl : 2 ≤ l) {V : Type*} [Fintype V] (G : SimpleGraph V) :
    2 * l * G.copyCount (SimpleGraph.cycleGraph (2 * l)) ≤
      G.copyCount (SimpleGraph.pathGraph (2 * l)) := by sorry

end EvenCycleTuran.PathCount
