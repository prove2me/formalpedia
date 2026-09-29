-- Prove2me | Theorems.Thm_CoresConvexGames_Stability_core_is_unique_stable_set
-- name    : CoresConvexGames.Stability.core_is_unique_stable_set
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:56:38.295849+00:00
-- url     : https://prove2.me/theorems/1fdc7c19-f93b-4e4c-92e0-dafd8eac2353
-- title:
--   Theorem 8 — the core of a convex game is its unique von Neumann–Morgenstern stable set
-- statement:
--   Let $N=\{1,\dots,n\}$ be a finite set of players and $v:2^N\to\mathbb R$ a game, i.e. a set function with $v(\emptyset)=0$. For a payoff vector $a\in\mathbb R^N$ and a coalition $S\subseteq N$ write $a(S)=\sum_{i\in S}a_i$. Suppose $v$ is **convex**: $v(S)+v(T)\le v(S\cup T)+v(S\cap T)$ for all $S,T\subseteq N$. A payoff vector $a$ is feasible if $a(N)\le v(N)$. The **core** $C$ is the set of feasible $a$ with $a(S)\ge v(S)$ for all $S\subseteq N$. A vector $a$ **dominates** $b$ if there is a nonempty coalition $S$ with $a(S)\le v(S)$ and $a_i>b_i$ for all $i\in S$. A set $V$ of feasible vectors is **stable** if every feasible vector is either a member of $V$ or dominated by a member of $V$, but not both.
--
--   Then the core of $v$ is stable, and it is the only stable set:
--
--   $$
--   C \text{ is stable},\qquad\text{and}\qquad V \text{ stable} \implies V=C .
--   $$
--
--   That is, the core of a convex game is its unique von Neumann–Morgenstern solution. For general games stable sets need not exist and need not be unique, so convexity singles out a class where the two classical solution concepts coincide.
--
--   **Formalization Note** Players are `Fin n` (a relabelling of Shapley's arbitrary finite $N$), a game is `f : Finset (Fin n) → ℝ`, and the core is the published `Supermodularity.Cooperative.Core Finset.univ f`. Convexity is the published `IsConvexGame f`, which includes $v(\emptyset)=0$. Stable sets are defined over feasible vectors, as on the page (a footnote notes the classical imputation-based variant gives the same answer for the core).
-- source:
--   Shapley, Cores of Convex Games, Int. J. Game Theory 1, 1971, https://doi.org/10.1007/BF01753431, p. 24, §4.3, Theorem 8

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_IsConvexGame
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_CoresConvexGames_Stability_IsStableSet

namespace CoresConvexGames.Stability

open Supermodularity.Cooperative

/-- Shapley (1971), p. 24, Theorem 8: the core of a convex game is stable, and it is the
unique stable set (von Neumann–Morgenstern solution). -/
theorem core_is_unique_stable_set {n : ℕ} (f : Finset (Fin n) → ℝ) (hf : IsConvexGame f) :
    IsStableSet f (Core Finset.univ f) ∧
      ∀ V : Set (Fin n → ℝ), IsStableSet f V → V = Core Finset.univ f := by sorry

end CoresConvexGames.Stability
