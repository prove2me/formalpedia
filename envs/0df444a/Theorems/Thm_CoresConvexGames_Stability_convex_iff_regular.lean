-- Prove2me | Theorems.Thm_CoresConvexGames_Stability_convex_iff_regular
-- name    : CoresConvexGames.Stability.convex_iff_regular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:53:49.948986+00:00
-- url     : https://prove2.me/theorems/d24c41e4-626d-4903-8b2a-882b86e784b2
-- title:
--   Theorem 5 — a game is convex iff its core configuration is regular
-- statement:
--   Let $N=\{1,\dots,n\}$ be a finite set of players and $v:2^N\to\mathbb R$ a game, i.e. a set function with $v(\emptyset)=0$. For a payoff vector $a\in\mathbb R^N$ and a coalition $S\subseteq N$ write $a(S)=\sum_{i\in S}a_i$. The core $C$ is the set of payoff vectors $a$ with $a(N)=v(N)$ and $a(S)\ge v(S)$ for all $S\subseteq N$; for $\emptyset\ne S\subseteq N$ the face $C_S$ is $\{a\in C: a(S)=v(S)\}$, and $C_\emptyset=C$. The game is **convex** if $v(S)+v(T)\le v(S\cup T)+v(S\cap T)$ for all $S,T\subseteq N$. The core configuration is **regular** if $C_N\ne\emptyset$ and $C_S\cap C_T\subseteq C_{S\cup T}\cap C_{S\cap T}$ for all $S,T\subseteq N$. Then
--
--   $$
--   v \text{ is convex} \iff \{C_S\} \text{ is regular}.
--   $$
--
--   The theorem translates the algebraic supermodularity condition on $v$ into a geometric condition on how the faces of the core fit together; the geometric results on regular configurations then apply to every convex game.
--
--   **Formalization Note** Players are `Fin n` (a relabelling of Shapley's arbitrary finite $N$), a game is `f : Finset (Fin n) → ℝ`, and the core is the published `Supermodularity.Cooperative.Core Finset.univ f`. "A game" is the single hypothesis $v(\emptyset)=0$. Convexity is the published `IsConvexGame f` ($v(\emptyset)=0$ and supermodularity on all of $2^N$).
-- source:
--   Shapley, Cores of Convex Games, Int. J. Game Theory 1, 1971, https://doi.org/10.1007/BF01753431, p. 22, §4.1, Theorem 5

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_IsConvexGame
import Definitions.Def_CoresConvexGames_Stability_IsRegularConfiguration

namespace CoresConvexGames.Stability

open Supermodularity.Cooperative

/-- Shapley (1971), p. 22, Theorem 5: a game (`v(O) = 0`) is convex if and only if its core
configuration is regular. -/
theorem convex_iff_regular {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0) :
    IsConvexGame f ↔ IsRegularConfiguration f := by sorry

end CoresConvexGames.Stability
