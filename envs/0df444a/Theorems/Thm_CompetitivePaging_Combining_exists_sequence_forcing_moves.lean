-- Prove2me | Theorems.Thm_CompetitivePaging_Combining_exists_sequence_forcing_moves
-- name    : CompetitivePaging.Combining.exists_sequence_forcing_moves
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:25:07.626111+00:00
-- url     : https://prove2.me/theorems/55dd580b-c1b7-4bd4-96fc-13fbbd7f2da1
-- title:
--   With $2m-1$ servers on $2m$ vertices an adversary forces a move at every step
-- statement:
--   Let $m\ge1$ and let $M$ be a set of $2m$ vertices with the uniform metric. For every deterministic on-line algorithm $A$ with $2m-1$ servers on $M$ and every $N\in\mathbb N$ there is a request sequence $\tau(N)$ of length $N$ that causes $A$ to move a server at every step; in particular
--   $$C_A(\tau(N))\ge N .$$
--
--   Together with the shuttle algorithms this gives the necessity half of Theorem 6: on $\tau(N)$ the algorithm $A$ pays at least $N$ while the $m$ shuttle algorithms together pay at most $N$.
--
--   **Formalization Note** The paper writes $C_A(\tau(N))=N$; equality holds for a lazy $A$, and for an arbitrary $A$ (which may move several servers at one step) the statement is the inequality, which is what the necessity argument uses. The vertex set is given by `e : Fin m × Fin 2 ≃ M`, as in the shuttle item.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 10 (PDF p. 11), §6, proof of Theorem 6 (necessity)

import Mathlib
import Definitions.Def_KServer_model

namespace CompetitivePaging.Combining

/-- Fiat et al. 1991, §6, proof of Theorem 6 (necessity), p. 10. With `2m − 1` servers on a
vertex set `M` of size `2m` (enumerated by `e : Fin m × Fin 2 ≃ M`) with the uniform metric,
for every deterministic on-line algorithm `A` and every `N` there is a request sequence `τ(N)` of
length `N` that causes `A` to move a server at every step; hence `C_A(τ(N)) ≥ N`. -/
theorem exists_sequence_forcing_moves {m : ℕ} (hm : 0 < m) {M : Type} [MetricSpace M]
    (hM : ∀ x y : M, x ≠ y → dist x y = 1) (e : Fin m × Fin 2 ≃ M)
    (A : KServer.OnlineAlgorithm (2 * m - 1) M) (N : ℕ) :
    ∃ τ : List M, τ.length = N ∧
      (∀ j < N, A.conf (τ.take j) ≠ A.conf (τ.take (j + 1))) ∧
      (N : ℝ) ≤ A.cost τ := by sorry

end CompetitivePaging.Combining
