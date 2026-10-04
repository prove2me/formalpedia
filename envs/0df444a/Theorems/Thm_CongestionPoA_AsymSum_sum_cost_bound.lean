-- Prove2me | Theorems.Thm_CongestionPoA_AsymSum_sum_cost_bound
-- name    : CongestionPoA.AsymSum.sum_cost_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:48:31.976503+00:00
-- url     : https://prove2.me/theorems/a79c1a1a-d649-44fc-a673-bf99a5e18a77
-- title:
--   Theorem 1, proof — summing over players: $\mathrm{SUM}(A) \le \sum_{e} n_e(P) f_e(n_e(A)+1)$
-- statement:
--   Let $G$ be a congestion game with linear latencies $f_e(k)=a_ek+b_e$, $a_e,b_e\ge0$, let $A$ be a pure Nash equilibrium of $G$, and let $P$ be any pure strategy profile. Then
--   $$\mathrm{SUM}(A)=\sum_{i\in N}c_i(A)\;\le\;\sum_{i\in N}\sum_{e\in P_i}f_e\bigl(n_e(A)+1\bigr)\;=\;\sum_{e\in E}n_e(P)\,f_e\bigl(n_e(A)+1\bigr).$$
--
--   The inequality sums the deviation inequality over all players; the equality regroups the double sum by facilities, each facility $e$ appearing once for each of the $n_e(P)$ players that use it in $P$. Lemma 1 then bounds the right-hand side, completing the proof of Theorem 1.
--
--   **Formalization Note** The paper writes this chain for the identity latency $f_e(k)=k$, as $\mathrm{SUM}(A)\le\sum_{i\in N}\sum_{e\in P_i}(n_e(A)+1)=\sum_{e\in E}n_e(P)(n_e(A)+1)$, and states that its proofs extend to general linear latencies; the statement here is that general case.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 3, Theorem 1, proof (sum over all players)

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model

namespace CongestionPoA.AsymSum

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 3, unnumbered step of the proof of Theorem 1 (summing over the players): at a pure Nash
equilibrium `A` of a linear congestion game, for any pure strategy profile `P`,
`SUM(A) = Σ_{i∈N} cᵢ(A) ≤ Σ_{i∈N} Σ_{e∈Pᵢ} f_e(n_e(A) + 1) = Σ_{e∈E} n_e(P) f_e(n_e(A) + 1)`.

**Formalization Note.** The paper prints this chain for the identity latency `f_e(k) = k`, as
`SUM(A) ≤ Σ_{i∈N} Σ_{e∈Pᵢ} (n_e(A) + 1) = Σ_{e∈E} n_e(P)(n_e(A) + 1)`, and says (Sect. 2, §1.1) that its
proofs extend to the general linear case `f_e(k) = a_e k + b_e`, `a_e, b_e ≥ 0`; the statement here is
that general case. -/
theorem sum_cost_bound {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (A P : ι → Finset E)
    (hlin : IsLinear G) (hA : IsPureNash G A) (hP : IsProfile G P) :
    sumCost G A ≤ ∑ i, ∑ e ∈ P i, G.latency e (load A e + 1) ∧
      ∑ i, ∑ e ∈ P i, G.latency e (load A e + 1) =
        ∑ e, (load P e : ℝ) * G.latency e (load A e + 1) := by sorry

end CongestionPoA.AsymSum
