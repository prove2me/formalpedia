-- Prove2me | Theorems.Thm_BalancedGames_Comb_theorem_8
-- name    : BalancedGames.Comb.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:22.047549+00:00
-- url     : https://prove2.me/theorems/587fe7f8-21b4-44c8-9c3d-3abadc80c6b9
-- title:
--   Theorem 8, p. 11 — a game in G+(n) is a vertex of BG+(n) iff it is balanced and 0-1-valued
-- statement:
--   Let $v\in\mathcal G_+(n)$, that is, a game on $N=\{1,\dots,n\}$ with $v(\varnothing)=0$, $v(S)\ge0$ for every coalition $S$ and $v(N)=1$. Then
--
--   $$v \text{ is a vertex of } \mathcal{BG}_+(n) \iff v \text{ is balanced and } v(S)\in\{0,1\}\ \text{for every } S\subseteq N .$$
--
--   Here a vertex is an extreme point of $\mathcal{BG}_+(n)$, the set of balanced games of $\mathcal G_+(n)$, and $v$ is balanced when its core is nonempty. The theorem identifies the vertices with the families $\mathcal D$ of proper coalitions on which $v$ equals $1$.
--
--   **Formalization Note** "0-1-valued" is checked on every coordinate, including $\varnothing$ and $N$, where it holds automatically in $\mathcal G_+(n)$.
--
--   Differences from the source:
--   - generalization: $N=\{1,\dots,n\}$ with $n\ge1$ implicit → every $n\in\mathbb N$; reason: at $n=0$, $\mathcal G_+(0)=\varnothing$ ($v(\varnothing)=0\neq1=v(N)$), so the statement is vacuous there and specializes to the paper's for $n\ge1$.
--   - encoding: game in $\mathbb R^{2^N\setminus\{\varnothing\}}$ → vector on all $2^n$ coalitions with $v(\varnothing)=0$ imposed in $\mathcal G_+(n)$; reason: an affine embedding, it preserves extreme points.
--   - encoding: balanced by (4) → nonempty core; reason: p. 4 identifies the two (Theorem 1).
--   - encoding: $N=\{1,\dots,n\}$ → `Fin n` (0-based); reason: relabelling of players.
-- source:
--   Garcia-Segador, Grabisch, Miranda, On the set of balanced games, arXiv:2501.14341v1, p. 11, Theorem 8

import Mathlib
import Definitions.Def_BalancedGames_Comb_Basic

namespace BalancedGames.Comb

/-- **Theorem 8** (p. 11). A game `v ∈ G+(n)` is a vertex (extreme point) of `BG+(n)` if and
only if `v` is balanced and 0-1-valued. -/
theorem theorem_8 (n : ℕ) (v : Game n) (hv : v ∈ Gplus n) :
    v ∈ Set.extremePoints ℝ (BGplus n) ↔ IsBalanced v ∧ IsZeroOne v := by sorry

end BalancedGames.Comb
