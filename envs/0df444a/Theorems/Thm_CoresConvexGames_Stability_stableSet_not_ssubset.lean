-- Prove2me | Theorems.Thm_CoresConvexGames_Stability_stableSet_not_ssubset
-- name    : CoresConvexGames.Stability.stableSet_not_ssubset
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:55:26.126993+00:00
-- url     : https://prove2.me/theorems/b75287bc-964a-4937-bc68-d29a56dfeb16
-- title:
--   §4.3 (p. 24) — no stable set properly includes another
-- statement:
--   Let $N=\{1,\dots,n\}$ be a finite set of players and $v:2^N\to\mathbb R$ a game, i.e. a set function with $v(\emptyset)=0$. For a payoff vector $a\in\mathbb R^N$ and a coalition $S\subseteq N$ write $a(S)=\sum_{i\in S}a_i$. A payoff vector is feasible if $a(N)\le v(N)$; $a$ dominates $b$ if some nonempty $S$ has $a(S)\le v(S)$ and $a_i>b_i$ for $i\in S$; a set $V$ of feasible vectors is stable if every feasible vector is either in $V$ or dominated by a member of $V$, but not both. If $V$ and $W$ are stable sets, then
--
--   $$
--   V\not\subsetneq W .
--   $$
--
--   Together with the fact that every stable set contains the core, this yields uniqueness of the stable set whenever the core itself is stable.
--
--   **Formalization Note** Players are `Fin n` (a relabelling of Shapley's arbitrary finite $N$), a game is `f : Finset (Fin n) → ℝ`, and the core is the published `Supermodularity.Cooperative.Core Finset.univ f`. The standing game assumption $v(\emptyset)=0$ is a hypothesis.
-- source:
--   Shapley, Cores of Convex Games, Int. J. Game Theory 1, 1971, https://doi.org/10.1007/BF01753431, p. 24, §4.3, paragraph after the definition of stable set, second sentence (unnumbered claim)

import Mathlib
import Definitions.Def_CoresConvexGames_Stability_IsStableSet

namespace CoresConvexGames.Stability

/-- Shapley (1971), p. 24, §4.3: no stable set properly includes another. -/
theorem stableSet_not_ssubset {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0)
    (V W : Set (Fin n → ℝ)) (hV : IsStableSet f V) (hW : IsStableSet f W) :
    ¬ V ⊂ W := by sorry

end CoresConvexGames.Stability
