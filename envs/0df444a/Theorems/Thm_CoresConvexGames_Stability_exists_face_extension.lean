-- Prove2me | Theorems.Thm_CoresConvexGames_Stability_exists_face_extension
-- name    : CoresConvexGames.Stability.exists_face_extension
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:52:03.431988+00:00
-- url     : https://prove2.me/theorems/68136413-4a66-482e-835f-426e06db92c3
-- title:
--   Lemma 2 — extending a face point by one player
-- statement:
--   Let $N=\{1,\dots,n\}$ be a finite set of players and $v:2^N\to\mathbb R$ a game, i.e. a set function with $v(\emptyset)=0$. For a payoff vector $a\in\mathbb R^N$ and a coalition $S\subseteq N$ write $a(S)=\sum_{i\in S}a_i$. The core $C$ is the set of payoff vectors $a$ with $a(N)=v(N)$ and $a(S)\ge v(S)$ for all $S\subseteq N$; for $\emptyset\ne S\subseteq N$ the face $C_S$ is $\{a\in C: a(S)=v(S)\}$, and $C_\emptyset=C$. Suppose the core configuration $\{C_S\}$ is regular. Let $S\subset\subset N$, i.e. $S\subsetneq N$ and $n-|S|\ge 2$, and let $a\in C_S$. Then for any $j\in N\setminus S$ there exists
--
--   $$
--   b\in C_S\cap C_{S\cup\{j\}}\qquad\text{with}\qquad b_i=a_i\ \text{ for all } i\in S .
--   $$
--
--   The lemma is the inductive step for building a point in the faces of a maximal chain of coalitions.
--
--   **Formalization Note** Players are `Fin n` (a relabelling of Shapley's arbitrary finite $N$), a game is `f : Finset (Fin n) → ℝ`, and the core is the published `Supermodularity.Cooperative.Core Finset.univ f`. $S\subset\subset N$ is encoded literally as `S ⊂ Finset.univ` together with `S.card + 2 ≤ n` (the first follows from the second). The standing game assumption $v(\emptyset)=0$ is a hypothesis.
-- source:
--   Shapley, Cores of Convex Games, Int. J. Game Theory 1, 1971, https://doi.org/10.1007/BF01753431, p. 19, §3.2, Lemma 2

import Mathlib
import Definitions.Def_CoresConvexGames_Stability_CoreFace
import Definitions.Def_CoresConvexGames_Stability_IsRegularConfiguration

namespace CoresConvexGames.Stability

/-- Shapley (1971), p. 19, Lemma 2. `S ⊂⊂ N` is `S ⊂ Finset.univ ∧ S.card + 2 ≤ n`. -/
theorem exists_face_extension {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0)
    (hreg : IsRegularConfiguration f) (S : Finset (Fin n)) (hS : S ⊂ Finset.univ)
    (hcard : S.card + 2 ≤ n) (a : Fin n → ℝ) (ha : a ∈ CoreFace f S)
    (j : Fin n) (hj : j ∉ S) :
    ∃ b ∈ CoreFace f S ∩ CoreFace f (insert j S), ∀ i ∈ S, b i = a i := by sorry

end CoresConvexGames.Stability
