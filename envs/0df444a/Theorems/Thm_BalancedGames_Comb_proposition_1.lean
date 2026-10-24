-- Prove2me | Theorems.Thm_BalancedGames_Comb_proposition_1
-- name    : BalancedGames.Comb.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:17.051289+00:00
-- url     : https://prove2.me/theorems/96016a9e-0c19-44eb-a2eb-ae4d3cb849ef
-- title:
--   Proposition 1, p. 11 — BG+(n) is a (2ⁿ − 2)-dimensional polytope
-- statement:
--   Let $n\ge 1$ and let $\mathcal{BG}_+(n)$ be the set of balanced games $v$ on $N=\{1,\dots,n\}$ with $v(\varnothing)=0$, $v\ge 0$ and $v(N)=1$. Then $\mathcal{BG}_+(n)$ is a polytope (the convex hull of finitely many games) and
--
--   $$\dim \mathcal{BG}_+(n) = 2^n-2 ,$$
--
--   where the dimension is that of the affine hull.
--
--   This is the setting for the vertex and edge results: $\mathcal{BG}_+(n)$ is a full-dimensional polytope in the $(2^n-2)$-dimensional space of free coordinates $v(S)$, $S\neq\varnothing,N$.
--
--   **Formalization Note** Games are vectors indexed by all $2^n$ coalitions, with the $\varnothing$ and $N$ coordinates fixed at $0$ and $1$; dimension is `Module.finrank` of the direction of the affine span.
--
--   Differences from the source:
--   - encoding: game in $\mathbb R^{2^N\setminus\{\varnothing\}}$ → vector on all $2^n$ coalitions with $v(\varnothing)=0$ imposed in $\mathcal G_+(n)$; reason: an affine embedding, it preserves convex hulls and affine dimension.
--   - encoding: balanced by the minimal-balanced-collection inequalities (4) → nonempty core; reason: p. 4 identifies the balanced games with those having a nonempty core (Theorem 1).
--   - encoding: polytope → convex hull of a finite set; reason: Minkowski–Weyl, the same sets as bounded polyhedra.
--   - encoding: $N=\{1,\dots,n\}$ → `Fin n` (0-based); reason: relabelling of players.
-- source:
--   Garcia-Segador, Grabisch, Miranda, On the set of balanced games, arXiv:2501.14341v1, p. 11, Proposition 1

import Mathlib
import Definitions.Def_BalancedGames_Comb_Basic

namespace BalancedGames.Comb

/-- **Proposition 1** (p. 11). For `n ≥ 1`, `BG+(n)` is a polytope (the convex hull of finitely
many games) and its affine dimension is `2ⁿ − 2`. -/
theorem proposition_1 (n : ℕ) (hn : 1 ≤ n) :
    IsPolytope (BGplus n) ∧
      Module.finrank ℝ (affineSpan ℝ (BGplus n)).direction = 2 ^ n - 2 := by sorry

end BalancedGames.Comb
