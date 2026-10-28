-- Prove2me | Theorems.Thm_DiscreteSearchGame_Optimal_theorem_6
-- name    : DiscreteSearchGame.Optimal.theorem_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:38.311394+00:00
-- url     : https://prove2.me/theorems/66ce0697-1934-4528-8ebb-c474fc533aaf
-- title:
--   Theorem 6, p. 11 — for any optimal p*, some optimal search strategy mixes at most n elements of 𝒞_{p*}
-- statement:
--   In the search game $G$ with $n$ boxes, search times $t_i>0$ and detection probabilities $q_i\in(0,1)$, for any optimal hiding strategy $p^*$ there is an optimal search strategy $\eta^*$, i.e. one with
--   $$V_i(\eta^*)\le v^*\qquad(i=1,\dots,n),$$
--   which is a mixture of at most $n$ Gittins search sequences against $p^*$, i.e. elements of $\mathcal C_{p^*}$.
--
--   In particular the searcher has an optimal strategy, so the infimum defining the searcher's side of the game is attained and equals the hider's value $v^*$.
--
--   **Formalization Note.** $v^*$ is the hider's max-inf (1). "Mixture of at most $n$ elements" means the PMF's support is contained in a finite set of at most $n$ sequences, all in $\mathcal C_{p^*}$.
-- source:
--   Clarkson, Lin & Glazebrook, A Classical Search Game in Discrete Locations, arXiv:2103.09310v1, p. 11, Theorem 6 (proof p. 12)

import Mathlib
import Definitions.Def_AllocationIndices_Jobs
import Definitions.Def_DiscreteSearchGame_Optimal_Model

open AllocationIndices Filter Topology

namespace DiscreteSearchGame.Optimal

/-- Theorem 6, p. 11: for any optimal hiding strategy `p*`, some optimal search strategy is a
mixture of at most `n` elements of `𝒞_{p*}`. -/
theorem theorem_6 {n : ℕ} (t q : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1)
    (p : Fin n → ℝ) (hp : IsOptimalHider t q p) :
    ∃ η : PMF (ℕ → Fin n), IsOptimalSearcher t q η ∧
      ∃ s : Finset (ℕ → Fin n), s.card ≤ n ∧
        (↑s : Set (ℕ → Fin n)) ⊆ {ξ | ConformsToSearchIndex p q t ξ} ∧ η.support ⊆ ↑s := by sorry

end DiscreteSearchGame.Optimal
