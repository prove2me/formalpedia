-- Prove2me | Theorems.Thm_CongestionPoA_SymMax_theorem7_deviation_bound
-- name    : CongestionPoA.SymMax.theorem7_deviation_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T09:10:55.56387+00:00
-- url     : https://prove2.me/theorems/4a7a6876-28d9-484b-a930-6e408e6699fa
-- title:
--   Theorem 7, proof — deviation to any optimal strategy $P_j$ in a symmetric game
-- statement:
--   Let $G$ be a symmetric congestion game with linear latencies $f_e(k)=a_ek+b_e$, $a_e,b_e\ge 0$. Let $A$ be a pure Nash equilibrium and $P$ any pure strategy profile. Then for all players $i$ and $j$,
--   $$c_i(A)\;\le\;\sum_{e\in P_j} f_e\big(n_e(A)+1\big).$$
--
--   Because the game is symmetric, $P_j$ is a strategy available to player $i$. This is the first display of the proof of Theorem 7, the comparison of an equilibrium cost with the cost of every strategy of the profile $P$.
--
--   **Formalization Note** The paper writes the inequality for the player of maximum cost and identity latencies (right side $\sum_{e\in P_j}(n_e(A)+1)$); here it is stated for every player and affine latencies.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 5, Theorem 7, proof (first display)

import Mathlib
import Definitions.Def_CongestionPoA_SymMax_Model

namespace CongestionPoA.SymMax

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 5, Theorem 7, proof (first display): in a symmetric linear congestion game, at a pure Nash
equilibrium `A` no player `i` gains by switching to the strategy `Pⱼ` of any player `j` in any pure
profile `P`, so
`cᵢ(A) ≤ cᵢ(A₋ᵢ, Pⱼ) ≤ Σ_{e∈Pⱼ} f_e(n_e(A) + 1)`.

**Formalization Note.** The paper writes this for player 1 (the player of maximum cost, "without loss
of generality") and identity latencies, where the right side is `Σ_{e∈Pⱼ}(n_e(A) + 1)`; here it is
stated for every player `i` and affine latencies `f_e(k) = a_e k + b_e`, `a_e, b_e ≥ 0`. Symmetry is
what makes `Pⱼ` an available strategy for player `i`. -/
theorem theorem7_deviation_bound {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (G : CongestionGame ι E) (A P : ι → Finset E)
    (hlin : IsLinear G) (hsym : IsSymmetric G) (hA : IsPureNash G A) (hP : IsProfile G P)
    (i j : ι) :
    cost G A i ≤ ∑ e ∈ P j, G.latency e (load A e + 1) := by sorry

end CongestionPoA.SymMax
