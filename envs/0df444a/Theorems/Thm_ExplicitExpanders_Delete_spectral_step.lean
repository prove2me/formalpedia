-- Prove2me | Theorems.Thm_ExplicitExpanders_Delete_spectral_step
-- name    : ExplicitExpanders.Delete.spectral_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:16:29.539657+00:00
-- url     : https://prove2.me/theorems/f420bdaf-651e-4eca-9000-0eff12736fe9
-- title:
--   Proof of Theorem 1.3 — $H'+M$ is an $(|V|-|U|, d, 2\sqrt{d-1}+\varepsilon)$-graph
-- statement:
--   Let $d\ge 3$, $\varepsilon>0$, and $r = \lceil 2/\varepsilon\rceil$. Let $H$ be an $(N, d, 2\sqrt{d-1}+\varepsilon/2)$-graph on a vertex set $V$ with $|V| = N$. Let $U\subseteq V$ satisfy the conclusions 2 and 3 of Lemma 3.1: the $(r+1)$-neighbourhood of every vertex of $U$ contains no cycle, and distinct vertices of $U$ are at distance at least $2r+3$. Let $m$ be any perfect matching on $N(U)$, and let $G$ be the graph obtained from $H$ by omitting $U$ and adding the matching edges $\{x,m(x)\}$, $x\in N(U)$. Then $G$ is an
--   $$\bigl(N - |U|,\; d,\; 2\sqrt{d-1}+\varepsilon\bigr)\text{-graph}.$$
--
--   This is the content of the proof of Theorem 1.3 on pp. 12–13, displays (8)–(11): "In order to complete the proof it remains to show that every nontrivial eigenvalue of $G$ has absolute value at most $2\sqrt{d-1}+\varepsilon$."
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, pp. 12–13, proof of Theorem 1.3, (8)–(11)

import Mathlib
import Definitions.Def_ExplicitExpanders_Delete_IsNDLambda
import Definitions.Def_ExplicitExpanders_Delete_Neighbourhoods
import Definitions.Def_ExplicitExpanders_Delete_DeleteAndMatch

namespace ExplicitExpanders.Delete

/-- Proof of Theorem 1.3, spectral step (Alon, arXiv:2003.11673v1, pp. 12–13, (8)–(11)): with
`r = ⌈2/ε⌉`, for every `U` satisfying conclusions 2–3 of Lemma 3.1 and every perfect matching `m`
on `N(U)`, the graph `G = H' + M` is an `(|V| - |U|, d, 2√(d-1) + ε)`-graph. -/
theorem spectral_step {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) (ε : ℝ) (hd : 3 ≤ d) (hε : 0 < ε)
    (hH : IsNDLambda H (Fintype.card V) d (2 * Real.sqrt ((d : ℝ) - 1) + ε / 2))
    (U : Finset V) (hU2 : ∀ z ∈ U, NoCycleOn H (ball H z (⌈2 / ε⌉₊ + 1)))
    (hU3 : ∀ z ∈ U, ∀ z' ∈ U, z ≠ z' → ((2 * ⌈2 / ε⌉₊ + 3 : ℕ) : ℕ∞) ≤ H.edist z z')
    (m : V → V) (hm : IsMatchingOn (nbrSet H U) m) :
    IsNDLambda (deleteAndMatch H U m) (Fintype.card V - U.card) d
      (2 * Real.sqrt ((d : ℝ) - 1) + ε) := by sorry

end ExplicitExpanders.Delete
