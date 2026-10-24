-- Prove2me | Theorems.Thm_BalancedGames_Comb_not_hypercube
-- name    : BalancedGames.Comb.not_hypercube
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:31.826826+00:00
-- url     : https://prove2.me/theorems/ab1b4a72-7527-4f04-ae35-481bfd4b074c
-- title:
--   Proof of Theorem 12, p. 19 — for n ≥ 2 the adjacency graph of BG+(n) is not a hypercube
-- statement:
--   Let $n\ge2$. The adjacency graph of $\mathcal{BG}_+(n)$ (its vertices as nodes, its edges as edges) is not isomorphic to any hypercube graph $Q_d$, $d\ge0$:
--
--   $$\mathrm{G}\big(\mathcal{BG}_+(n)\big)\not\cong Q_d\qquad\text{for every } d\ge 0 .$$
--
--   This is the step of the proof of Theorem 12 that rules out the first alternative of Theorem 11 (Naddef–Pulleyblank). For $n=1$ the polytope is a single point, whose graph is $Q_0$; this is why $n\ge2$ is required, and the proof treats $n=1$ separately.
--
--   **Formalization Note** The proof passage argues $n=2$ by counting (3 vertices) and $n\ge3$ by exhibiting the vertices $\hat\delta_{\{i\}}=\delta_{\{i\}}+\delta_N$, $\hat\delta_{\{j\}}$ whose sum minus $\delta_N$ is not a vertex; the claim formalized is the conclusion of the passage, not the observation it uses.
--
--   Differences from the source:
--   - reading: the passage settles $n=1$ trivially and shows "not a hypercube" for $n=2$ and $n\ge3$ → for every $n\ge2$ the adjacency graph of $\mathcal{BG}_+(n)$ is not graph-isomorphic to any $Q_d$; reason: an unnumbered claim of the proof; this is what the passage asserts.
--   - encoding: game in $\mathbb R^{2^N\setminus\{\varnothing\}}$ → vector on all $2^n$ coalitions with $v(\varnothing)=0$ imposed in $\mathcal G_+(n)$; reason: an affine embedding, it preserves vertices and edges.
--   - encoding: balanced by (4) → nonempty core; reason: p. 4 identifies the two (Theorem 1).
--   - encoding: $N=\{1,\dots,n\}$ → `Fin n` (0-based); reason: relabelling of players.
-- source:
--   Garcia-Segador, Grabisch, Miranda, On the set of balanced games, arXiv:2501.14341v1, p. 19, proof of Theorem 12 (non-hypercube step)

import Mathlib
import Definitions.Def_BalancedGames_Comb_Basic

namespace BalancedGames.Comb

/-- **Proof of Theorem 12** (p. 19), the non-hypercube step: for `n ≥ 2` the adjacency graph of
`BG+(n)` is not isomorphic to any hypercube graph `Q_d`. -/
theorem not_hypercube (n : ℕ) (hn : 2 ≤ n) : ¬ IsHypercube (adjGraph (BGplus n)) := by sorry

end BalancedGames.Comb
