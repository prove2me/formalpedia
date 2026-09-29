-- Prove2me | Theorems.Thm_CoresConvexGames_Stability_exists_intermediate_face
-- name    : CoresConvexGames.Stability.exists_intermediate_face
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:51:01.318992+00:00
-- url     : https://prove2.me/theorems/61541166-dbfc-418b-83bc-39a4f723e09f
-- title:
--   Lemma 1 — an intermediate face between $C_S$ and $C_T$
-- statement:
--   Let $N=\{1,\dots,n\}$ be a finite set of players and $v:2^N\to\mathbb R$ a game, i.e. a set function with $v(\emptyset)=0$. For a payoff vector $a\in\mathbb R^N$ and a coalition $S\subseteq N$ write $a(S)=\sum_{i\in S}a_i$. The core $C$ is the set of payoff vectors $a$ with $a(N)=v(N)$ and $a(S)\ge v(S)$ for all $S\subseteq N$; for $\emptyset\ne S\subseteq N$ the face $C_S$ is $\{a\in C: a(S)=v(S)\}$, and $C_\emptyset=C$. Write $S\subset\subset T$ if $S\subsetneq T$ and $|T|-|S|\ge 2$. Suppose the core configuration $\{C_S\}$ is regular.
--
--   If $S\subset\subset T$ and $a\in C_S\cap C_T$, then for any two distinct preassigned players $j,k\in T\setminus S$ there exist a coalition $Q$ and a payoff vector $b$ with
--
--   $$
--   S\subsetneq Q\subsetneq T,\qquad b\in C_S\cap C_Q\cap C_T,\qquad b_i=a_i\ (i\in S),\qquad j\in Q,\ k\notin Q .
--   $$
--
--   The lemma inserts an intermediate coalition between two nested coalitions whose faces meet; it is the step that lets chains of coalitions be refined one player at a time.
--
--   **Formalization Note** Players are `Fin n` (a relabelling of Shapley's arbitrary finite $N$), a game is `f : Finset (Fin n) → ℝ`, and the core is the published `Supermodularity.Cooperative.Core Finset.univ f`. The hypothesis $j\ne k$ is implicit in the page's "two preassigned elements" (for $j=k$ the conclusion $j\in Q$, $k\notin Q$ is impossible). The standing game assumption $v(\emptyset)=0$ is a hypothesis.
-- source:
--   Shapley, Cores of Convex Games, Int. J. Game Theory 1, 1971, https://doi.org/10.1007/BF01753431, p. 18, §3.2, Lemma 1 (including the "Moreover" clause)

import Mathlib
import Definitions.Def_CoresConvexGames_Stability_CoreFace
import Definitions.Def_CoresConvexGames_Stability_IsRegularConfiguration

namespace CoresConvexGames.Stability

/-- Shapley (1971), p. 18, Lemma 1 (with its "Moreover" clause). `S ⊂⊂ T` is
`S ⊂ T ∧ S.card + 2 ≤ T.card`; the two preassigned elements `j, k` of `T − S` are distinct. -/
theorem exists_intermediate_face {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0)
    (hreg : IsRegularConfiguration f) (S T : Finset (Fin n)) (hST : S ⊂ T)
    (hcard : S.card + 2 ≤ T.card) (a : Fin n → ℝ) (ha : a ∈ CoreFace f S ∩ CoreFace f T)
    (j k : Fin n) (hj : j ∈ T \ S) (hk : k ∈ T \ S) (hjk : j ≠ k) :
    ∃ (Q : Finset (Fin n)) (b : Fin n → ℝ), S ⊂ Q ∧ Q ⊂ T ∧
      b ∈ CoreFace f S ∩ CoreFace f Q ∩ CoreFace f T ∧
      (∀ i ∈ S, b i = a i) ∧ j ∈ Q ∧ k ∉ Q := by sorry

end CoresConvexGames.Stability
