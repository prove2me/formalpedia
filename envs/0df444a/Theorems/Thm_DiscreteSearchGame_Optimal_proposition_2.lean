-- Prove2me | Theorems.Thm_DiscreteSearchGame_Optimal_proposition_2
-- name    : DiscreteSearchGame.Optimal.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:08.947057+00:00
-- url     : https://prove2.me/theorems/927731ba-4c97-48d8-9326-c52e15d2d7bd
-- title:
--   Proposition 2, p. 7 — an optimal search strategy mixes only Gittins search sequences against every optimal hiding strategy
-- statement:
--   Consider the search game $G$ with $n$ boxes, search times $t_i>0$ and detection probabilities $q_i\in(0,1)$, value $v^*$, and let $\mathcal P^*$ be the set of optimal hiding strategies. Let $\eta^*$ be an optimal search strategy, i.e. $V_i(\eta^*)\le v^*$ for every box $i$. Then every search sequence $\xi$ played by $\eta^*$ with positive probability is a Gittins search sequence against every optimal hiding strategy:
--   $$\eta^*(\xi)>0\ \Longrightarrow\ \xi\in\bigcap_{p\in\mathcal P^*}\mathcal C_p .$$
--   An optimal searcher can therefore only use sequences that optimally counter every optimal hider.
--
--   **Formalization Note.** Optimality of $\eta^*$ is `IsOptimalSearcher` (every coordinate of $V(\eta^*)$ at most the hider's max-inf value) and optimality of $p$ is `IsOptimalHider`; $\xi\in\mathcal C_p$ is `ConformsToSearchIndex p q t ξ`.
-- source:
--   Clarkson, Lin & Glazebrook, A Classical Search Game in Discrete Locations, arXiv:2103.09310v1, p. 7, Proposition 2

import Mathlib
import Definitions.Def_AllocationIndices_Jobs
import Definitions.Def_DiscreteSearchGame_Optimal_Model

open AllocationIndices Filter Topology

namespace DiscreteSearchGame.Optimal

/-- Proposition 2, p. 7: every optimal search strategy mixes only search sequences that are
Gittins search sequences against every optimal hiding strategy. -/
theorem proposition_2 {n : ℕ} (t q : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1)
    (η : PMF (ℕ → Fin n)) (hη : IsOptimalSearcher t q η) :
    ∀ ξ ∈ η.support, ∀ p, IsOptimalHider t q p → ConformsToSearchIndex p q t ξ := by sorry

end DiscreteSearchGame.Optimal
