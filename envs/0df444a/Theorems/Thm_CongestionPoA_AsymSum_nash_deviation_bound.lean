-- Prove2me | Theorems.Thm_CongestionPoA_AsymSum_nash_deviation_bound
-- name    : CongestionPoA.AsymSum.nash_deviation_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:48:44.639455+00:00
-- url     : https://prove2.me/theorems/f7a3ca0e-9282-41e0-957f-d3151135d2c1
-- title:
--   Theorem 1, proof — deviation inequality $c_i(A) \le c_i(A_{-i},P_i) \le \sum_{e\in P_i} f_e(n_e(A)+1)$
-- statement:
--   Let $G$ be a congestion game with linear latencies $f_e(k)=a_ek+b_e$, $a_e,b_e\ge0$, let $A$ be a pure Nash equilibrium of $G$, and let $P$ be any pure strategy profile. Then for every player $i$,
--   $$c_i(A)\;\le\; c_i(A_{-i},P_i)\;\le\;\sum_{e\in P_i} f_e\bigl(n_e(A)+1\bigr),$$
--   where $(A_{-i},P_i)$ is the profile obtained from $A$ by replacing $A_i$ with $P_i$.
--
--   The first inequality is the Nash condition for the deviation of player $i$ to $P_i$; the second bounds the cost of that deviation by the loads of the equilibrium. It is the first step of the proof of Theorem 1, and the inequality that is summed over the players.
--
--   **Formalization Note** The paper writes this chain for the identity latency $f_e(k)=k$, as $c_i(A)=\sum_{e\in A_i}n_e(A)\le\sum_{e\in P_i}n_e(A_{-i},P_i)\le\sum_{e\in P_i}(n_e(A)+1)$, and states that its proofs extend to general linear latencies; the statement here is that general case.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 3, Theorem 1, proof (deviation inequality)

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model

namespace CongestionPoA.AsymSum

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 3, unnumbered step of the proof of Theorem 1 (the deviation inequality): at a pure Nash
equilibrium `A` of a linear congestion game, for any pure strategy profile `P` and any player `i`,
`cᵢ(A) ≤ cᵢ(A₋ᵢ, Pᵢ) ≤ Σ_{e∈Pᵢ} f_e(n_e(A) + 1)`.

**Formalization Note.** The paper prints this chain for the identity latency `f_e(k) = k`, as
`cᵢ(A) = Σ_{e∈Aᵢ} n_e(A) ≤ Σ_{e∈Pᵢ} n_e(A₋ᵢ, Pᵢ) ≤ Σ_{e∈Pᵢ} (n_e(A) + 1)`, and says (Sect. 2, §1.1) that
its proofs extend to the general linear case `f_e(k) = a_e k + b_e`, `a_e, b_e ≥ 0`; the statement
here is that general case, with `f_e(n_e(A) + 1)` in place of `n_e(A) + 1`. `(A₋ᵢ, Pᵢ)` is
`Function.update A i (P i)`. Profiles are maps `ι → Finset E`; `IsProfile G P` says `Pᵢ ∈ Σᵢ`. -/
theorem nash_deviation_bound {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (A P : ι → Finset E)
    (hlin : IsLinear G) (hA : IsPureNash G A) (hP : IsProfile G P) (i : ι) :
    cost G A i ≤ cost G (Function.update A i (P i)) i ∧
      cost G (Function.update A i (P i)) i ≤ ∑ e ∈ P i, G.latency e (load A e + 1) := by sorry

end CongestionPoA.AsymSum
