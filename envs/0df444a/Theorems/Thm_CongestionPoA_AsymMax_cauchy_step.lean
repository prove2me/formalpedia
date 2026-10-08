-- Prove2me | Theorems.Thm_CongestionPoA_AsymMax_cauchy_step
-- name    : CongestionPoA.AsymMax.cauchy_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T17:32:42.748394+00:00
-- url     : https://prove2.me/theorems/3730d23b-e9c1-4dce-b58a-db2ea1366f4a
-- title:
--   Theorem 5, proof — weighted load-square bound
-- statement:
--   For any pure profile $A$ and any finite facility set $Q$ in a game with nonnegative affine latencies $f_e(n)=a_en+b_e$,
--
--   $$\left(\sum_{e\in Q}a_e n_e(A)\right)^2\le \left(\sum_{e\in Q}a_e\right)\operatorname{SUM}(A).$$
--
--   This is the coefficient-weighted form of the Cauchy–Schwarz step in the maximum-cost upper bound. Under identity latencies the coefficient sum is $|Q|$.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 4, Theorem 5, proof, Cauchy–Schwarz step

import Definitions.Def_CongestionPoA_AsymMax_Model

set_option autoImplicit false

namespace CongestionPoA.AsymMax

/-- Christodoulou and Koutsoupias, STOC 2005, Theorem 5, proof,
Cauchy–Schwarz step, PDF p. 4. Formalization Note: the paper's `|P₁|` is
the total coefficient weight for affine latencies; `Q` may be any set of
facilities, and the inequality holds for any profile. -/
theorem cauchy_step {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (a b : E → ℝ)
    (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e)
    (hlat : ∀ e n, G.latency e n = a e * n + b e)
    (A : ι → Finset E) (Q : Finset E) :
    (∑ e ∈ Q, a e * (load A e : ℝ)) ^ 2 ≤
      (∑ e ∈ Q, a e) * sumCost G A := by sorry

end CongestionPoA.AsymMax
