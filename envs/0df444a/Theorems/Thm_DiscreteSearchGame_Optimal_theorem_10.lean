-- Prove2me | Theorems.Thm_DiscreteSearchGame_Optimal_theorem_10
-- name    : DiscreteSearchGame.Optimal.theorem_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:43.662307+00:00
-- url     : https://prove2.me/theorems/bad6392d-bb50-4346-b3c0-45806db4a4ef
-- title:
--   Theorem 10, p. 20 — for any optimal hiding strategy p*, some optimal search strategy mixes at most n elements of 𝒞̂_{p*}
-- statement:
--   Consider the search game $G$: a hider hides in one of $n$ boxes; a search of box $i$ takes time $t_i>0$ and finds a hider there with probability $q_i\in(0,1)$; the payoff is the time to detection. Let $v^*=\sup_{p}\inf_{\xi}\sum_ip_iV_i(\xi)$ be the value, and let $p^*$ be an optimal hiding strategy. Then there is a search strategy $\eta^*$ with
--   $$V_i(\eta^*)\le v^*\qquad(i=1,\dots,n)$$
--   that is a mixture of at most $n$ elements of
--   $$\widehat{\mathcal C}_{p^*}=\{\xi_{\sigma,p^*}:\sigma\in S_n\},$$
--   the Gittins search sequences against $p^*$ that break every tie using one and the same preference ordering $\sigma$.
--
--   Hence, to construct an optimal search strategy it suffices to consider the at most $n!$ sequences $\xi_{\sigma,p^*}$; this is what makes the finite subgame $G_{\widehat{\mathcal C}_p}$ of §5 an exact optimality test.
--
--   **Formalization Note.** `[NeZero n]` is needed to construct $\xi_{\sigma,p}$ and is implied by $p^*$ lying in the simplex. $\xi_{\sigma,p}$ is `simpleSeq`: at every search it takes, among the boxes of maximal Gittins index $p_i(1-q_i)^{m_i}q_i/t_i$, the one listed first by $\sigma$ (read as position ↦ box). Searcher optimality is pinned to the hider's max-inf value (1), so the statement also asserts that the searcher's infimum is attained at $v^*$.
-- source:
--   Clarkson, Lin & Glazebrook, A Classical Search Game in Discrete Locations, arXiv:2103.09310v1, p. 20, Theorem 10 (proof pp. 20–21)

import Mathlib
import Definitions.Def_AllocationIndices_Jobs
import Definitions.Def_DiscreteSearchGame_Optimal_Model

open AllocationIndices Filter Topology

namespace DiscreteSearchGame.Optimal

/-- Theorem 10, p. 20: for any optimal hiding strategy `p*`, some optimal search strategy is a
mixture of at most `n` elements of `𝒞̂_{p*}`, Gittins search sequences against `p*` that break
every tie by one preference ordering. -/
theorem theorem_10 {n : ℕ} [NeZero n] (t q : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1)
    (p : Fin n → ℝ) (hp : IsOptimalHider t q p) :
    ∃ η : PMF (ℕ → Fin n), IsOptimalSearcher t q η ∧
      ∃ s : Finset (ℕ → Fin n), s.card ≤ n ∧
        (↑s : Set (ℕ → Fin n)) ⊆ simpleGittins t q p ∧ η.support ⊆ ↑s := by sorry

end DiscreteSearchGame.Optimal
