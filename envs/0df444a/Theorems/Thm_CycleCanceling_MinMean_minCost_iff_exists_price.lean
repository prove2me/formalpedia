-- Prove2me | Theorems.Thm_CycleCanceling_MinMean_minCost_iff_exists_price
-- name    : CycleCanceling.MinMean.minCost_iff_exists_price
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:12:19.917428+00:00
-- url     : https://prove2.me/theorems/86d315c5-5ca5-405a-a5c0-03937fc05a3b
-- title:
--   Theorem 3.1 — minimum-cost iff some price function satisfies the optimality constraints (4)
-- statement:
--   Let $f$ be a circulation in a circulation network $G=(V,E)$ with residual capacities $u_f$ and reduced costs $c_p(v,w)=c(v,w)+p(v)-p(w)$. Then $f$ is minimum-cost if and only if there is a price function $p:V\to\mathbb R$ such that
--   $$
--   u_f(v,w)>0\ \Longrightarrow\ c_p(v,w)\ge 0\qquad\forall (v,w)\in E\qquad(\text{optimality constraints (4)}).
--   $$
--   This is linear-programming duality (complementary slackness) specialized to minimum-cost circulations, due to Ford and Fulkerson. It shows that $0$-optimality is optimality.
-- source:
--   Goldberg, Tarjan, Finding Minimum-Cost Circulations by Canceling Negative Cycles, J. ACM 36(4), 1989, p. 877, Theorem 3.1, Eq. (4)

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_Network
import Definitions.Def_CycleCanceling_MinMean_EpsOptimal

namespace CycleCanceling.MinMean

/-- Theorem 3.1 (p. 877): a circulation `f` is minimum-cost if and only if there is a price
function `p` with `u_f(v, w) > 0 ⇒ c_p(v, w) ≥ 0` for all `(v, w) ∈ E` (optimality
constraints (4)). -/
theorem minCost_iff_exists_price {V : Type*} [Fintype V] [DecidableEq V]
    (N : CircNetwork V) (f : V → V → ℝ) (hf : IsCirculation N f) :
    IsMinCost N f ↔ ∃ p : V → ℝ, ∀ v w, (v, w) ∈ N.E → 0 < resCap N f v w →
      0 ≤ reducedCost N p v w := by sorry

end CycleCanceling.MinMean
