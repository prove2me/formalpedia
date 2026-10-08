-- Prove2me | Theorems.Thm_CongestionPoA_AsymMax_inequality1
-- name    : CongestionPoA.AsymMax.inequality1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T17:32:27.273926+00:00
-- url     : https://prove2.me/theorems/68e528c4-e23a-41d7-93e9-2a5f8cec8c7b
-- title:
--   Theorem 5, inequality (1) — unilateral-deviation bound
-- statement:
--   Let $A$ be a pure Nash profile and $P$ any feasible profile in a finite congestion game with latencies $f_e(n)=a_en+b_e$, where $a_e,b_e\ge0$. For every player $i$,
--
--   $$c_i(A)\le \sum_{e\in P_i} a_e n_e(A)+c_i(P).$$
--
--   This bounds the cost of an equilibrium player by the loads on the facilities in a comparison strategy and that player's comparison cost.
--
--   **Formalization Note** The paper displays the identity-latency case for player 1. The coefficient-weighted form covers its stated affine convention and is valid for every player.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 4, Theorem 5, proof, inequality (1)

import Definitions.Def_CongestionPoA_AsymMax_Model

set_option autoImplicit false

namespace CongestionPoA.AsymMax

/-- Christodoulou and Koutsoupias, STOC 2005, Theorem 5, proof,
inequality (1), PDF p. 4. Formalization Note: an arbitrary player replaces the
paper's player 1. The coefficient-weighted term is the affine-latency form of
the printed identity-latency sum. -/
theorem inequality1 {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (a b : E → ℝ)
    (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e)
    (hlat : ∀ e n, G.latency e n = a e * n + b e)
    (A P : ι → Finset E) (hA : IsPureNash G A) (hP : IsProfile G P)
    (i : ι) :
    cost G A i ≤ (∑ e ∈ P i, a e * (load A e : ℝ)) + cost G P i := by sorry

end CongestionPoA.AsymMax
