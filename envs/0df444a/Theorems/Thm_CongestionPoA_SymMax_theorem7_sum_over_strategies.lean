-- Prove2me | Theorems.Thm_CongestionPoA_SymMax_theorem7_sum_over_strategies
-- name    : CongestionPoA.SymMax.theorem7_sum_over_strategies
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T09:11:23.704347+00:00
-- url     : https://prove2.me/theorems/efbc8184-b895-4076-b99f-b0bcc58cd0ba
-- title:
--   Theorem 7, proof — summing over $j$: $N\cdot c_i(A)\le\sum_e n_e(P)f_e(n_e(A)+1)$
-- statement:
--   Let $G$ be a symmetric congestion game with $N$ players and linear latencies $f_e(k)=a_ek+b_e$, $a_e,b_e\ge 0$. Let $A$ be a pure Nash equilibrium and $P$ any pure strategy profile. Then for every player $i$,
--   $$N\cdot c_i(A)\;\le\;\sum_{e\in E} n_e(P)\,f_e\big(n_e(A)+1\big).$$
--
--   This is the second display of the proof of Theorem 7 ("If we sum these inequalities for every $j$"); it turns the per-strategy comparison into a bound by a single sum over facilities.
--
--   **Formalization Note** $N$ is the number of players. The paper's version is for the player of maximum cost and identity latencies (right side $\sum_e n_e(P)(n_e(A)+1)$).
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 5, Theorem 7, proof (second display)

import Mathlib
import Definitions.Def_CongestionPoA_SymMax_Model

namespace CongestionPoA.SymMax

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 5, Theorem 7, proof (second display): summing the deviation inequalities over every `j ∈ N`,
`N · cᵢ(A) ≤ Σ_{e∈E} n_e(P) f_e(n_e(A) + 1)`.

**Formalization Note.** `N` is the number of players `Fintype.card ι`. The paper states it for player 1
and identity latencies (right side `Σ_e n_e(P)(n_e(A) + 1)`); here it is for every player `i` and
affine latencies `f_e(k) = a_e k + b_e`, `a_e, b_e ≥ 0`. -/
theorem theorem7_sum_over_strategies {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (G : CongestionGame ι E) (A P : ι → Finset E)
    (hlin : IsLinear G) (hsym : IsSymmetric G) (hA : IsPureNash G A) (hP : IsProfile G P)
    (i : ι) :
    (Fintype.card ι : ℝ) * cost G A i ≤ ∑ e, (load P e : ℝ) * G.latency e (load A e + 1) := by sorry

end CongestionPoA.SymMax
