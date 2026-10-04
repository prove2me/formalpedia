-- Prove2me | Theorems.Thm_Aumann1987_TwoPerson_player2_iff_ineq_2_5
-- name    : Aumann1987.TwoPerson.player2_iff_ineq_2_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:27:48.752782+00:00
-- url     : https://prove2.me/theorems/34bc50a2-e3a6-447e-b4fd-3d07f9d4a6ab
-- title:
--   Proposition 2.3, proof — player 2's condition (2.2) is equivalent to (2.5)
-- statement:
--   Let $(p_{jk})$ be a distribution on $S^1\times S^2$ and $h^2$ player 2's payoff. Player 2's equilibrium condition (2.2) written on $p$ — for every $\psi:S^2\to S^2$, $\sum_j\sum_k p_{jk}h^2_{j\psi(k)}\le\sum_j\sum_k p_{jk}h^2_{jk}$ — holds if and only if
--
--   $$\sum_j\big(h^2_{jk}-h^2_{jr}\big)p_{jk}\ \ge\ 0\qquad\text{for all }k,r\in S^2,$$
--
--   the second inequality of Proposition 2.3, which the proof calls (2.5).
-- source:
--   Aumann, Correlated Equilibrium as an Expression of Bayesian Rationality, Econometrica 55 (1987), DOI 10.2307/1911154, p. 6 (PDF p. 7), Proposition 2.3, proof (player 2 gives (2.5))

import Mathlib
import Definitions.Def_Aumann1987_TwoPerson_Model

open Finset

namespace Aumann1987.TwoPerson

/-- **Player 2 gives (2.5)** (Aumann 1987, Proposition 2.3, proof, p. 6, PDF p. 7: "Similarly, (2.5)
is seen to express the equilibrium condition (2.2) for i = 2"). For a distribution `p`, player 2's
equilibrium condition (2.2) written on `p` holds iff `∑_j (h²_{jk} − h²_{jr}) p_{jk} ≥ 0` for all
`k, r ∈ S²`.

Formalization Note: the second inequality of Proposition 2.3 carries no printed label; the proof
calls it (2.5). -/
theorem player2_iff_ineq_2_5 {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    (h₂ : S₁ → S₂ → ℝ) (p : S₁ → S₂ → ℝ) (hp : IsDistribution p) :
    DevCond₂ h₂ p ↔ ∀ k r : S₂, 0 ≤ ∑ j, (h₂ j k - h₂ j r) * p j k := by sorry

end Aumann1987.TwoPerson
