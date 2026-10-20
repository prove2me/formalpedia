-- Prove2me | Theorems.Thm_BrandSpillover_Commitment_committed_game
-- name    : BrandSpillover.Commitment.committed_game
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:59.07326+00:00
-- url     : https://prove2.me/theorems/4ce83d30-9ee7-4cb1-bde7-0c45f15a39a4
-- title:
--   §4.4, p. 17, and proof of Proposition 4, p. 34 — with commitment the CM always induces (O, O); Firm W's profit
-- statement:
--   Assume the standing assumptions, and suppose Firm W commits to not using brand spillover, so that the spillover level is $0$. Then the CM always induces both firms to outsource: an equilibrium with structure $(O,O)$ exists, and every equilibrium has structure $(O,O)$. At every equilibrium Firm W's profit is
--
--   $$\Pi^{oo}_W\big|_{\alpha=0} = \begin{cases} \Big(\dfrac{2\theta - 1 - c}{3}\Big)^2 & \text{if } c \le \tfrac12(2\theta-1),\\[6pt] \Big(\dfrac{2\theta-1}{6}\Big)^2 & \text{otherwise.}\end{cases}$$
--
--   This is the benchmark against which Proposition 4 compares the game without commitment.
--
--   **Formalization Note** The proof of Proposition 4 lists the second formula only for $c \le c^{oo}_2|_{\alpha=0} = \tfrac12$. Under the standing assumptions $c$ can be as large as $5/7$; for $c > \tfrac12$ Lemma 3 gives the prices $(\tfrac12, \tfrac\theta2)$ and the same profit, so the statement covers every admissible $c$.
-- source:
--   Wu, Zhang & Zhou, Brand Spillover as a Marketing Strategy, SSRN preprint 3891915 (June 2021), p. 17 (§4.4) and p. 34 (proof of Proposition 4)

import Mathlib
import Definitions.Def_BrandSpillover_Commitment_Model

namespace BrandSpillover.Commitment

/-- §4.4, p. 17, and proof of Proposition 4, p. 34: when Firm W commits to not using brand
spillover (spillover level `0`), the CM always induces `(O, O)`, and Firm W's equilibrium profit
is `((2θ − 1 − c)/3)²` if `c ≤ (2θ − 1)/2` and `((2θ − 1)/6)²` otherwise. -/
theorem committed_game (P : Params) (hP : P.Standing) :
    (∃ w : ℝ × ℝ, IsEquilibrium P 0 .OO w) ∧
    ∀ (s : Structure) (w : ℝ × ℝ), IsEquilibrium P 0 s w →
      s = .OO ∧
      profitW P 0 s w = if P.c ≤ (2 * P.θ - 1) / 2 then ((2 * P.θ - 1 - P.c) / 3) ^ 2
        else ((2 * P.θ - 1) / 6) ^ 2 := by sorry

end BrandSpillover.Commitment
