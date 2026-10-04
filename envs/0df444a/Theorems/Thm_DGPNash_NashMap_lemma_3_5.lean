-- Prove2me | Theorems.Thm_DGPNash_NashMap_lemma_3_5
-- name    : DGPNash.NashMap.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:04:32.466834+00:00
-- url     : https://prove2.me/theorems/4067f65d-8bd3-4154-8d71-9b39543c3349
-- title:
--   Lemma 3.5 — variation of a pure-strategy payoff
-- statement:
--   Fix a player $p$ and pure strategy $j$ in a finite game with at least two players, nonempty finite strategy sets, and nonnegative payoffs. For any two mixed profiles $x,x'$, the variation in the payoff from playing $j$ against the opponents obeys
--
--   $$|U^p_j(x)-U^p_j(x')|\le \bigl(\max_{s_{-p}}u^p_{js}\bigr)\sum_{q\ne p}\sum_{i\in S_q}|x^q_i-x'^q_i|.$$
--
--   This bounds the sensitivity of expected pure-strategy payoffs to changes in opponents' strategies and supplies a component of the Lipschitz estimate for Nash's map.
--
--   **Formalization Note** Unlike the other statements in this mission, this lemma allows a different finite strategy type $S_q$ for each player $q$, as the paper's wording does.
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), p. 205, Lemma 3.5; https://doi.org/10.1137/070699652

import Definitions.Def_DGPNash_NashMap_nashMap

namespace DGPNash.NashMap

open Finset

/-- Lemma 3.5, p. 205: the payoff of a fixed pure strategy is Lipschitz in opponents' lotteries. -/
theorem lemma_3_5 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Nonempty (S i)] (hr : 2 ≤ Fintype.card ι)
    (u : ι → (∀ i, S i) → ℝ) (hu : ∀ p s, 0 ≤ u p s)
    (x x' : ∀ i, S i → ℝ)
    (hx : AGT.IsMixedProfile x) (hx' : AGT.IsMixedProfile x')
    (p : ι) (j : S p) :
    |purePayoff u x p j - purePayoff u x' p j| ≤
      maxPurePayoff u p j *
        ∑ q : ι, if q = p then 0 else ∑ i : S q, |x q i - x' q i| := by sorry

end DGPNash.NashMap
