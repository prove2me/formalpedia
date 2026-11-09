-- Prove2me | Theorems.Thm_AnonymousDirectedCounting_Exact_matching_leader_vistas
-- name    : AnonymousDirectedCounting.Exact.matching_leader_vistas
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:49.747162+00:00
-- url     : https://prove2.me/theorems/ae09faf2-c699-44ff-b821-bd9200a16113
-- title:
--   Theorem 4 — matching multi-leader indistinguishability
-- statement:
--   For every $n>\ell\ge2$ there are dynamic networks of orders $n$ and $n+\ell-1$, each with exactly $\ell$ leaders, with designated leaders $x$ and $x'$ whose vistas are identical through round $2n-3$. Every round graph of both networks is a strongly connected loopless directed multigraph, with arc multiplicities at most $\ell$ and outdegrees at most $\ell^2$. This is the indistinguishability behind the lower bound $2n-2$.
--
--   Differences from the source:
--   - encoding: anonymous agents and abstract history-tree nodes with fibers → external Fin n indexing, and nodes as values of History r with fibers computed from the network; reason: the index is absent from protocol inputs; two agents have equal History r exactly when they lie in one class of P_r, so nodes and vistas up to isomorphism are the same data
--   - encoding: identical vistas through round 2n − 3 → equal History t values for every t ≤ 2n − 3; reason: History t is the vista up to the isomorphism of printed p. 4
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), Theorem 4, printed p. 21 (PDF p. 23)

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_HistoryTree

set_option autoImplicit false

namespace AnonymousDirectedCounting.Exact

/-- Theorem 4, printed p. 21 (PDF p. 23). For `n > ℓ ≥ 2` there are dynamic networks of orders `n`
and `n + ℓ - 1`, each with exactly `ℓ` leaders, whose designated leaders have identical vistas
through round `2n - 3`; every round graph is strongly connected (in `Admissible`), loopless, with
arc multiplicities at most `ℓ` and outdegrees at most `ℓ ^ 2`. -/
theorem matching_leader_vistas (n ell : ℕ) (hell : 2 ≤ ell) (hn : ell < n) :
    ∃ (G : NetworkModel n) (G' : NetworkModel (n + ell - 1)) (x : Fin n) (x' : Fin (n + ell - 1)),
      Admissible G ∧ Admissible G' ∧ G.leaders.card = ell ∧ G'.leaders.card = ell ∧
      x ∈ G.leaders ∧ x' ∈ G'.leaders ∧
      LooplessBoundedRounds G ell ∧ LooplessBoundedRounds G' ell ∧
      ∀ t : ℕ, t ≤ 2 * n - 3 → history G t x = history G' t x' := by sorry

end AnonymousDirectedCounting.Exact
