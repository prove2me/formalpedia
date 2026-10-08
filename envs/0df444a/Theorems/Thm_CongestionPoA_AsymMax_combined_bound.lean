-- Prove2me | Theorems.Thm_CongestionPoA_AsymMax_combined_bound
-- name    : CongestionPoA.AsymMax.combined_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T17:32:52.730963+00:00
-- url     : https://prove2.me/theorems/403fb446-bbab-4d30-82f8-7f305f23a582
-- title:
--   Theorem 5, proof — square-root player-cost bound
-- statement:
--   Let $A$ be a pure Nash profile and $P$ any feasible profile in a finite congestion game with $f_e(n)=a_en+b_e$, $a_e,b_e\ge0$. For every player $i$,
--
--   $$c_i(A)\le c_i(P)+\sqrt{\frac52\left(\sum_{e\in P_i}a_e\right)\operatorname{SUM}(P)}.$$
--
--   This is the intermediate player-cost estimate used to obtain the maximum social-cost upper bound.
--
--   **Formalization Note** The paper prints $|P_1|$ for identity latencies; the coefficient sum is its affine-latency counterpart.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 4, Theorem 5, proof, combined bound

import Definitions.Def_CongestionPoA_AsymMax_Model

set_option autoImplicit false

namespace CongestionPoA.AsymMax

/-- Christodoulou and Koutsoupias, STOC 2005, Theorem 5, proof,
combined bound after inequality (1), PDF p. 4. Formalization Note: the
coefficient-weighted sum replaces `|P₁|` for affine latencies, and `i`
is an arbitrary player. -/
theorem combined_bound {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (a b : E → ℝ)
    (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e)
    (hlat : ∀ e n, G.latency e n = a e * n + b e)
    (A P : ι → Finset E) (hA : IsPureNash G A) (hP : IsProfile G P)
    (i : ι) :
    cost G A i ≤ cost G P i +
      Real.sqrt ((5 / 2 : ℝ) * (∑ e ∈ P i, a e) * sumCost G P) := by sorry

end CongestionPoA.AsymMax
