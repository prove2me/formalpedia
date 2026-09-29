-- Prove2me | Theorems.Thm_CoresConvexGames_Stability_dominated_by_core_of_not_mem_core
-- name    : CoresConvexGames.Stability.dominated_by_core_of_not_mem_core
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:55:54.463787+00:00
-- url     : https://prove2.me/theorems/50123951-38a7-4612-9eb3-de2020e52146
-- title:
--   Proof of Theorem 8 (p. 24) — a feasible vector outside the core is dominated by a core point
-- statement:
--   Let $N=\{1,\dots,n\}$ be a finite set of players and $v:2^N\to\mathbb R$ a game, i.e. a set function with $v(\emptyset)=0$. For a payoff vector $a\in\mathbb R^N$ and a coalition $S\subseteq N$ write $a(S)=\sum_{i\in S}a_i$. Suppose $v$ is convex: $v(S)+v(T)\le v(S\cup T)+v(S\cap T)$ for all $S,T$. Let $C$ be the core ($a(N)=v(N)$ and $a(S)\ge v(S)$ for all $S$), call $b$ feasible if $b(N)\le v(N)$, and say that $a$ dominates $b$ if some nonempty $S$ has $a(S)\le v(S)$ and $a_i>b_i$ for all $i\in S$. Then every feasible $b\notin C$ is dominated by an element of $C$:
--
--   $$
--   b(N)\le v(N),\ b\notin C\ \Longrightarrow\ \exists\,a\in C:\ a \text{ dominates } b .
--   $$
--
--   This is the external stability of the core of a convex game, the substantive half of Theorem 8.
--
--   **Formalization Note** Players are `Fin n` (a relabelling of Shapley's arbitrary finite $N$), a game is `f : Finset (Fin n) → ℝ`, and the core is the published `Supermodularity.Cooperative.Core Finset.univ f`. The paper's proof starts from a regular configuration; the hypothesis here is convexity, which is the hypothesis of Theorem 8 whose proof this is (regularity follows by Theorem 5, and the last step of the proof uses the convexity inequality directly).
-- source:
--   Shapley, Cores of Convex Games, Int. J. Game Theory 1, 1971, https://doi.org/10.1007/BF01753431, p. 24, §4.3, proof of Theorem 8, first paragraph (first two sentences)

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_IsConvexGame
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_CoresConvexGames_Stability_IsFeasible
import Definitions.Def_CoresConvexGames_Stability_Dominates

namespace CoresConvexGames.Stability

open Supermodularity.Cooperative

/-- Shapley (1971), p. 24, §4.3, proof of Theorem 8, first paragraph: in a convex game,
every feasible payoff vector outside the core is dominated by an element of the core. -/
theorem dominated_by_core_of_not_mem_core {n : ℕ} (f : Finset (Fin n) → ℝ)
    (hf : IsConvexGame f) (b : Fin n → ℝ) (hb : IsFeasible f b)
    (hbC : b ∉ Core Finset.univ f) :
    ∃ a ∈ Core Finset.univ f, Dominates f a b := by sorry

end CoresConvexGames.Stability
