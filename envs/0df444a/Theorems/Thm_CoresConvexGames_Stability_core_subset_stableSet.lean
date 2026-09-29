-- Prove2me | Theorems.Thm_CoresConvexGames_Stability_core_subset_stableSet
-- name    : CoresConvexGames.Stability.core_subset_stableSet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:54:32.294+00:00
-- url     : https://prove2.me/theorems/b3d88a73-f4b1-44d5-ac51-c55a70e121ec
-- title:
--   §4.3 (p. 24) — every stable set contains the core
-- statement:
--   Let $N=\{1,\dots,n\}$ be a finite set of players and $v:2^N\to\mathbb R$ a game, i.e. a set function with $v(\emptyset)=0$. For a payoff vector $a\in\mathbb R^N$ and a coalition $S\subseteq N$ write $a(S)=\sum_{i\in S}a_i$. A payoff vector is feasible if $a(N)\le v(N)$; the core $C$ is the set of feasible $a$ with $a(S)\ge v(S)$ for all $S$; $a$ dominates $b$ if some nonempty $S$ has $a(S)\le v(S)$ and $a_i>b_i$ for $i\in S$; and a set $V$ of feasible vectors is stable if every feasible vector is either in $V$ or dominated by a member of $V$, but not both. Then for every stable set $V$,
--
--   $$
--   C\subseteq V .
--   $$
--
--   Combined with the fact that no stable set properly includes another, it shows that if the core is stable then it is the only stable set.
--
--   **Formalization Note** Players are `Fin n` (a relabelling of Shapley's arbitrary finite $N$), a game is `f : Finset (Fin n) → ℝ`, and the core is the published `Supermodularity.Cooperative.Core Finset.univ f`. The standing game assumption $v(\emptyset)=0$ is a hypothesis.
-- source:
--   Shapley, Cores of Convex Games, Int. J. Game Theory 1, 1971, https://doi.org/10.1007/BF01753431, p. 24, §4.3, paragraph after the definition of stable set, first sentence (unnumbered claim)

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_CoresConvexGames_Stability_IsStableSet

namespace CoresConvexGames.Stability

open Supermodularity.Cooperative

/-- Shapley (1971), p. 24, §4.3: every stable set contains the core. -/
theorem core_subset_stableSet {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0)
    (V : Set (Fin n → ℝ)) (hV : IsStableSet f V) :
    Core Finset.univ f ⊆ V := by sorry

end CoresConvexGames.Stability
