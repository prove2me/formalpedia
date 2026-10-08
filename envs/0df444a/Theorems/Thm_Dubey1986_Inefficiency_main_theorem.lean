-- Prove2me | Theorems.Thm_Dubey1986_Inefficiency_main_theorem
-- name    : Dubey1986.Inefficiency.main_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:33:37.035866+00:00
-- url     : https://prove2.me/theorems/75c33fa9-57ce-43da-85f8-9dbd6fc6367a
-- title:
--   Theorem, p. 3 — for an open dense set of $C^2$ payoffs: finitely many N.E., an efficient N.E. has a player at a vertex, a strong N.E. at most one player off a vertex
-- statement:
--   Let $n\ge2$ players have strategy sets the unit simplices $S^i=\{x\in\mathbb R^{k(i)}_+:\sum_j x_j\le1\}$, $k(i)\ge1$, let $V^i\supseteq S^i$ be open neighbourhoods, and let $(U)^n$ be the space of games whose payoffs are $C^2$ on $V=V^1\times\dots\times V^n$ with finite $C^2$-norm. There is an open dense set $U_0$ of $(U)^n$ such that, for $u\in U_0$:
--   1. $N(u)$ is a finite set;
--   2. if $s=(s^1,\dots,s^n)\in N(u)\cap E(u)$, then at least one $s^j$ is a vertex of $S^j$;
--   3. if $s=(s^1,\dots,s^n)\in G(u)$, then at most one $s^j$ is not a vertex of $S^j$.
--
--   In words: for generic smooth payoffs, Nash equilibria are isolated and finite, and they are Pareto-inefficient unless some player sits at a vertex of his strategy set; strong equilibria force all but at most one player to a vertex.
--
--   **Formalization Note** "Open dense" is in the product of the $C^2$-norm topologies (see the definition file). The neighbourhoods $V^i$ are open. Part 3 is stated as "if $s^i$ and $s^j$ are both not vertices then $i=j$".
-- source:
--   Dubey, Inefficiency of Nash Equilibria, IIASA WP-83-74 (July 1983), p. 3, Theorem

import Mathlib
import Definitions.Def_Dubey1986_Inefficiency_Setting

namespace Dubey1986.Inefficiency

theorem main_theorem {n : ℕ} (hn : 2 ≤ n) (k : Fin n → ℕ) (hk : ∀ i, 1 ≤ k i)
    (V : ∀ i, Set (Fin (k i) → ℝ)) (hVo : ∀ i, IsOpen (V i))
    (hSV : ∀ i, simplex (k i) ⊆ V i) :
    ∃ U₀ : Set (Fin n → Strat k → ℝ), IsOpenDense V U₀ ∧ ∀ u ∈ U₀,
      (NashSet u).Finite ∧
      (∀ s ∈ NashSet u ∩ EffSet u, ∃ j, IsVertex (k j) (s j)) ∧
      (∀ s ∈ StrongNashSet u, ∀ i j,
        ¬ IsVertex (k i) (s i) → ¬ IsVertex (k j) (s j) → i = j) := by sorry

end Dubey1986.Inefficiency
