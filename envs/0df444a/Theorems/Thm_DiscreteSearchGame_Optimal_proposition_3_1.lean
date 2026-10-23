-- Prove2me | Theorems.Thm_DiscreteSearchGame_Optimal_proposition_3_1
-- name    : DiscreteSearchGame.Optimal.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:13.460987+00:00
-- url     : https://prove2.me/theorems/4a176a74-5d35-4204-806c-2ff88b1cfd01
-- title:
--   Proposition 3 [1.] only, p. 7 — an optimal hiding strategy hides in every box with positive probability
-- statement:
--   In the search game $G$ with $n$ boxes, search times $t_i>0$ and detection probabilities $q_i\in(0,1)$, if $p^*=(p^*_1,\dots,p^*_n)$ is an optimal hiding strategy, then
--   $$p^*_i>0\qquad\text{for } i=1,\dots,n.$$
--   This is part [1.] of Proposition 3; it lets every later result about optimal hiding strategies work with interior points of the simplex, where all expected detection times of Gittins search sequences are finite.
--
--   **Formalization Note.** Parts [2.] and [3.] of Proposition 3 are not part of this statement. Optimality is `IsOptimalHider`: $p$ lies in the simplex and $\inf_\xi\sum_ip_iV_i(\xi)$ equals the value.
-- source:
--   Clarkson, Lin & Glazebrook, A Classical Search Game in Discrete Locations, arXiv:2103.09310v1, p. 7, Proposition 3 [1.]

import Mathlib
import Definitions.Def_AllocationIndices_Jobs
import Definitions.Def_DiscreteSearchGame_Optimal_Model

open AllocationIndices Filter Topology

namespace DiscreteSearchGame.Optimal

/-- Proposition 3 [1.], p. 7: an optimal hiding strategy hides in every box with positive
probability. -/
theorem proposition_3_1 {n : ℕ} (t q : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1)
    (p : Fin n → ℝ) (hp : IsOptimalHider t q p) : ∀ i, 0 < p i := by sorry

end DiscreteSearchGame.Optimal
