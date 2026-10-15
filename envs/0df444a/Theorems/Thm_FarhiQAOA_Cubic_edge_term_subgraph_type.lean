-- Prove2me | Theorems.Thm_FarhiQAOA_Cubic_edge_term_subgraph_type
-- name    : FarhiQAOA.Cubic.edge_term_subgraph_type
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:31:04.460137+00:00
-- url     : https://prove2.me/theorems/8d9954e0-1e0f-4882-9571-a87ec92a6ec8
-- title:
--   Section II, (18) and (23), p. 5 — at p = 1 an edge term of a 3-regular graph is f_g4, f_g5 or f_g6
-- statement:
--   Let $G$ be a 3-regular graph on $n$ vertices and $\langle jk\rangle$ an edge of $G$. For $p=1$ and angles $\gamma,\beta\in\mathbb R$, write
--   $$e_{jk}(\gamma,\beta) = \langle\gamma,\beta|\,C_{\langle jk\rangle}\,|\gamma,\beta\rangle$$
--   for the term of $\langle jk\rangle$ in the edge sum (13) of $F_1$. Let $\lambda$ be the number of common neighbours of $j$ and $k$. Then
--
--   1. if $\lambda = 2$, $e_{jk}(\gamma,\beta) = f_{g_4}(\gamma,\beta)$;
--   2. if $\lambda = 1$, $e_{jk}(\gamma,\beta) = f_{g_5}(\gamma,\beta)$;
--   3. if $\lambda = 0$, $e_{jk}(\gamma,\beta) = f_{g_6}(\gamma,\beta)$.
--
--   This is the case $p=1$, degree 3, of the paper's observation that each edge term depends only on the isomorphism type of the subgraph $g(j,k)$ formed by the qubits within distance $p$ of the edge ((16), (23)): "if two edges $\langle jk\rangle$ and $\langle j'k'\rangle$ give rise to isomorphic subgraphs, then the corresponding functions of $(\boldsymbol\gamma,\boldsymbol\beta)$ are the same". Figure (18) lists the three types that occur, and they are told apart by $\lambda$. This reduction of an $n$-qubit expectation to a fixed-size one is what makes the analysis of §V possible.
--
--   **Formalization Note** The common-neighbour count is how the three pictures of (18) are distinguished; it is a description of the figure, not an added hypothesis. Neither connectivity nor $n\neq 4$ is assumed: the statement holds for $K_4$, where every edge has two common neighbours.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm, arXiv:1411.4028v1, p. 5, Section II, figure (18), (23) and the sentence after (23)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_FarhiQAOA_Cubic_Types

namespace FarhiQAOA.Cubic

open QAlgorithms

/-- Farhi–Goldstone–Gutmann, Section II, p. 5, figure (18) and (23): in a 3-regular graph, for
`p = 1` the term of an edge `⟨jk⟩` in the edge sum (13) depends only on the subgraph type of the edge:
it equals `f_{g₄}`, `f_{g₅}` or `f_{g₆}` according as `j` and `k` have 2, 1 or 0 common neighbours. -/
theorem edge_term_subgraph_type {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (j k : Fin n) (hjk : G.Adj j k) (γ β : ℝ) :
    (commonNbrCount G j k = 2 → edgeTerm1 G γ β j k = fg4 γ β) ∧
      (commonNbrCount G j k = 1 → edgeTerm1 G γ β j k = fg5 γ β) ∧
      (commonNbrCount G j k = 0 → edgeTerm1 G γ β j k = fg6 γ β) := by sorry

end FarhiQAOA.Cubic
