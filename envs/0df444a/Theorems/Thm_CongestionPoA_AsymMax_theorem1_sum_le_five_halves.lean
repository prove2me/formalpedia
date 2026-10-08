-- Prove2me | Theorems.Thm_CongestionPoA_AsymMax_theorem1_sum_le_five_halves
-- name    : CongestionPoA.AsymMax.theorem1_sum_le_five_halves
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T17:32:52.288503+00:00
-- url     : https://prove2.me/theorems/9fd2d385-6337-4151-89d3-da3af1ad3d0d
-- title:
--   Theorem 1 — total-cost bound of 5/2
-- statement:
--   In any finite congestion game with nonnegative affine latencies, let $A$ be a pure Nash profile and $P$ any feasible profile. Then
--
--   $$\operatorname{SUM}(A)\le\frac52\operatorname{SUM}(P).$$
--
--   The paper states this as a bound for average social cost; the same inequality holds for total cost because averaging divides both sides by the number of players. It supplies the total-cost estimate used in Theorem 5.
--
--   **Formalization Note** This local restatement uses this mission's game model. If mission I's version is published first, it may be replaced by a compatible reference after comparison of the definitions.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 3, Theorem 1; invoked PDF p. 4, Theorem 5, proof

import Definitions.Def_CongestionPoA_AsymMax_Model

set_option autoImplicit false

namespace CongestionPoA.AsymMax

/-- Christodoulou and Koutsoupias, STOC 2005, Theorem 1, PDF p. 3;
invoked in Theorem 5's proof, PDF p. 4. Formalization Note: total cost is
`N` times the paper's average cost, and `P` is any feasible profile.
The affine nonnegative latency convention is from Sect. 2, PDF p. 2. -/
theorem theorem1_sum_le_five_halves {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (A P : ι → Finset E)
    (hlin : IsLinear G) (hA : IsPureNash G A) (hP : IsProfile G P) :
    sumCost G A ≤ (5 / 2 : ℝ) * sumCost G P := by sorry

end CongestionPoA.AsymMax
