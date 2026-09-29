-- Prove2me | Theorems.Thm_CoresConvexGames_Stability_chain_faces_inter_nonempty
-- name    : CoresConvexGames.Stability.chain_faces_inter_nonempty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:52:54.168077+00:00
-- url     : https://prove2.me/theorems/de3da809-d3f7-4c5e-a35e-34d3b9516293
-- title:
--   Theorem 2 — faces along an increasing chain meet; regular implies complete
-- statement:
--   Let $N=\{1,\dots,n\}$ be a finite set of players and $v:2^N\to\mathbb R$ a game, i.e. a set function with $v(\emptyset)=0$. For a payoff vector $a\in\mathbb R^N$ and a coalition $S\subseteq N$ write $a(S)=\sum_{i\in S}a_i$. The core $C$ is the set of payoff vectors $a$ with $a(N)=v(N)$ and $a(S)\ge v(S)$ for all $S\subseteq N$; for $\emptyset\ne S\subseteq N$ the face $C_S$ is $\{a\in C: a(S)=v(S)\}$, and $C_\emptyset=C$. Suppose the core configuration $\{C_S\}$ is regular. Then for any strictly increasing sequence of coalitions $S_1\subsetneq S_2\subsetneq\cdots\subsetneq S_m$ ($m\ge1$),
--
--   $$
--   C_{S_1}\cap C_{S_2}\cap\cdots\cap C_{S_m}\ne\emptyset .
--   $$
--
--   In particular (take $m=1$), a regular core configuration is complete: every face $C_S$ is nonempty.
--
--   This is the basic geometric consequence of regularity. It is what places the marginal vectors in the core and supplies the core points on prescribed hyperplanes used in the proofs of Theorems 3, 5 and 8.
--
--   **Formalization Note** Players are `Fin n` (a relabelling of Shapley's arbitrary finite $N$), a game is `f : Finset (Fin n) → ℝ`, and the core is the published `Supermodularity.Cooperative.Core Finset.univ f`. A sequence of length $m\ge1$ is a map `Fin (m + 1) → Finset (Fin n)`, and "increasing" is `StrictMono` (strict inclusion). The "in particular" clause is stated as a second conjunct. The standing game assumption $v(\emptyset)=0$ is a hypothesis.
-- source:
--   Shapley, Cores of Convex Games, Int. J. Game Theory 1, 1971, https://doi.org/10.1007/BF01753431, p. 18, §3.2, Theorem 2, equation (15)

import Mathlib
import Definitions.Def_CoresConvexGames_Stability_CoreFace
import Definitions.Def_CoresConvexGames_Stability_IsCompleteConfiguration
import Definitions.Def_CoresConvexGames_Stability_IsRegularConfiguration

namespace CoresConvexGames.Stability

/-- Shapley (1971), p. 18, Theorem 2: in a regular core configuration, the faces along any
strictly increasing sequence `S_1 ⊂ S_2 ⊂ ⋯ ⊂ S_m` (`m ≥ 1`) of coalitions have a common
point; in particular (`m = 1`) a regular core configuration is complete. -/
theorem chain_faces_inter_nonempty {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0)
    (hreg : IsRegularConfiguration f) :
    (∀ (m : ℕ) (S : Fin (m + 1) → Finset (Fin n)), StrictMono S →
      (⋂ k, CoreFace f (S k)).Nonempty) ∧
    IsCompleteConfiguration f := by sorry

end CoresConvexGames.Stability
