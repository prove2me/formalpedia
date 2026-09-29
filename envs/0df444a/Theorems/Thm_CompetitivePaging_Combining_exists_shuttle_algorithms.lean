-- Prove2me | Theorems.Thm_CompetitivePaging_Combining_exists_shuttle_algorithms
-- name    : CompetitivePaging.Combining.exists_shuttle_algorithms
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:24:34.477322+00:00
-- url     : https://prove2.me/theorems/32752201-556a-407a-ad5f-8527e52fd381
-- title:
--   $m$ shuttle algorithms on $2m$ vertices whose total cost never exceeds the number of requests
-- statement:
--   Let $m\ge1$, let $M$ be a set of $2m$ vertices with the uniform metric, and number its vertices so that vertex $i$ and vertex $i+m$ form the $i$-th pair, $i=1,\dots,m$. Consider $2m-1$ servers. There are deterministic on-line algorithms $B(1),\dots,B(m)$ such that
--
--   1. $B(i)$ keeps every vertex other than $i$ and $i+m$ covered at all times, and
--   2. at every step of every request sequence the movement costs of $B(1),\dots,B(m)$ add up to at most $1$: no two of them move a server at the same step, and each moves at most one server; and
--   3. consequently, for every request sequence $\sigma$,
--   $$\sum_{i=1}^m C_{B(i)}(\sigma)\le|\sigma| .$$
--
--   These are the shuttle algorithms of the necessity half of Theorem 6: $B(i)$ moves its one free server between $i$ and $i+m$, and no two of them ever have to move at the same step.
--
--   **Formalization Note** The pairing is given by a bijection `e : Fin m × Fin 2 ≃ M`: `e (i, 0)` and `e (i, 1)` are the paper's vertices $i$ and $i+m$. The number of servers $2m-1$ is a natural-number subtraction, which is exact because $m\ge1$.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, pp. 9–10 (PDF pp. 10–11), §6, proof of Theorem 6 (necessity)

import Mathlib
import Definitions.Def_KServer_model

namespace CompetitivePaging.Combining

/-- Fiat et al. 1991, §6, proof of Theorem 6 (necessity), pp. 9–10. Vertex set `M` of size
`2m`, enumerated by `e : Fin m × Fin 2 ≃ M` (`e (i, 0)` and `e (i, 1)` are the paper's
vertices `i` and `i + m`), with the uniform metric; `2m − 1` servers. There are deterministic
on-line algorithms `B(1), …, B(m)` such that `B(i)` keeps every vertex other than `e (i, 0)`,
`e (i, 1)` covered at all times; at every step of every request sequence the movement costs of
all of them add up to at most `1` (no two of them ever move a server at the same step, and each
moves at most one server); hence on every request sequence `σ` their total cost is at most the
length of `σ`. -/
theorem exists_shuttle_algorithms {m : ℕ} (hm : 0 < m) {M : Type} [MetricSpace M]
    (hM : ∀ x y : M, x ≠ y → dist x y = 1) (e : Fin m × Fin 2 ≃ M) :
    ∃ B : Fin m → KServer.OnlineAlgorithm (2 * m - 1) M,
      (∀ (i : Fin m) (l : List M) (x : M), x ≠ e (i, 0) → x ≠ e (i, 1) →
          ∃ j, (B i).conf l j = x) ∧
      (∀ (σ : List M) (s : ℕ), s < σ.length →
          ∑ i, KServer.moveCost ((B i).conf (σ.take s)) ((B i).conf (σ.take (s + 1))) ≤ 1) ∧
      ∀ σ : List M, ∑ i, (B i).cost σ ≤ (σ.length : ℝ) := by sorry

end CompetitivePaging.Combining
