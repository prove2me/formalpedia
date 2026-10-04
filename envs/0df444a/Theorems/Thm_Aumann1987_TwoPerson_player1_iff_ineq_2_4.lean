-- Prove2me | Theorems.Thm_Aumann1987_TwoPerson_player1_iff_ineq_2_4
-- name    : Aumann1987.TwoPerson.player1_iff_ineq_2_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:27:41.426202+00:00
-- url     : https://prove2.me/theorems/622a3a3a-a289-474e-b3bc-9ba6ab1686fb
-- title:
--   Proposition 2.3, proof — player 1's condition (2.2) is equivalent to (2.4)
-- statement:
--   Let $(p_{jk})$ be a distribution on $S^1\times S^2$ and $h^1$ player 1's payoff. Player 1's equilibrium condition (2.2) written on $p$ — for every $\varphi:S^1\to S^1$, $\sum_j\sum_k p_{jk}h^1_{\varphi(j)k}\le\sum_j\sum_k p_{jk}h^1_{jk}$ — holds if and only if
--
--   $$\sum_k\big(h^1_{jk}-h^1_{qk}\big)p_{jk}\ \ge\ 0\qquad\text{for all }j,q\in S^1,$$
--
--   which is condition (2.4) of Proposition 2.3. For an impossible suggestion $j$ (all $p_{jk}=0$) the inequality reads $0\ge0$.
-- source:
--   Aumann, Correlated Equilibrium as an Expression of Bayesian Rationality, Econometrica 55 (1987), DOI 10.2307/1911154, p. 6 (PDF p. 7), Proposition 2.3, proof (player 1 gives (2.4))

import Mathlib
import Definitions.Def_Aumann1987_TwoPerson_Model

open Finset

namespace Aumann1987.TwoPerson

/-- **Player 1 gives (2.4)** (Aumann 1987, Proposition 2.3, proof, p. 6, PDF p. 7). For a
distribution `p`, player 1's equilibrium condition (2.2) written on `p` holds iff
`∑_k (h¹_{jk} − h¹_{qk}) p_{jk} ≥ 0` for all `j, q ∈ S¹`, which is (2.4).

Formalization Note: the paper says "multiply through by `Σⱼ pⱼₖ`"; the factor is `Σₖ pⱼₖ`
(misprint). For an impossible `j` all `p_{jk} = 0` and (2.4) reads `0 ≥ 0`. -/
theorem player1_iff_ineq_2_4 {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    (h₁ : S₁ → S₂ → ℝ) (p : S₁ → S₂ → ℝ) (hp : IsDistribution p) :
    DevCond₁ h₁ p ↔ ∀ j q : S₁, 0 ≤ ∑ k, (h₁ j k - h₁ q k) * p j k := by sorry

end Aumann1987.TwoPerson
