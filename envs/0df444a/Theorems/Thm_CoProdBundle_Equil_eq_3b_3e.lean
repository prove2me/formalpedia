-- Prove2me | Theorems.Thm_CoProdBundle_Equil_eq_3b_3e
-- name    : CoProdBundle.Equil.eq_3b_3e
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:31.387521+00:00
-- url     : https://prove2.me/theorems/c2e3e7fb-230c-4431-9620-92ed474846e6
-- title:
--   (3b)–(3e), p. 15 — the retailer's unique optimal price P*(Q) = (2A+bc)Q^θ/(3b), demand, profit, and S(Q) = (2/b)((A−bc)Q^θ/3)^{3/2}
-- statement:
--   Let $b > 0$, $A - bw > 0$, $0 < \theta < 2/3$ and $0 < \gamma < 1$. For a bundle of $Q$ value units, the retailer sets the price $P$ to maximize its profit $\Pi_R(P,Q) = (1-\gamma)(P - wQ^\theta)\sqrt{AQ^\theta - bP}$.
--
--   1. For every $Q > 0$ the retailer's optimal price is unique and equals
--   $$P^*(Q) = \frac{2A + bw}{3b}\,Q^\theta. \qquad (3b)$$
--   2. At this price demand is $D^*(Q) = \sqrt{\tfrac{A-bw}{3}\,Q^\theta}$ (3c), and the retailer's profit is
--   $$\Pi_R^*(Q) = \frac{2}{b}(1-\gamma)\Bigl(\frac{A-bw}{3}\,Q^\theta\Bigr)^{3/2}. \qquad (3d)$$
--   3. For every $Q \ge 0$ the sharable surplus is
--   $$S(Q) = \frac{2}{b}\Bigl(\frac{A-bw}{3}\,Q^\theta\Bigr)^{3/2}. \qquad (3e)$$
--
--   This is the retailer's stage of the backward solution. Formula (3e) is what turns each producer's revenue share $\gamma (Q_i/Q) S(Q)$ into the explicit payoff (4a) that the producers' game is solved with.
--
--   **Formalization Note** The paper's distribution-cost coefficient $c$ is `w`. $S(Q)$ is defined as the supremum of the surplus over all real prices, so part 3 is a genuine optimization statement. It is stated also at $Q = 0$, where both sides are $0$, because a producer's deviation can make the aggregate output $0$.
-- source:
--   Bhargava, Bundling for Flexibility and Variety: An Economic Model for Multiproducer Value Aggregation, author's accepted manuscript (2020; Manag. Sci. doi:10.1287/mnsc.2020.3662), §4.1, (3a)–(3e), p. 15

import Mathlib
import Definitions.Def_CoProdBundle_Equil_Setting

namespace CoProdBundle.Equil

/-- (3b)–(3e), p. 15: the retailer's unique optimal price, the demand, its profit, and the
sharable surplus at its optimum. -/
theorem eq_3b_3e (A b w θ γ : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hθ0 : 0 < θ)
    (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (∀ Q : ℝ, 0 < Q →
      (IsRetailerOptimal γ A b w θ Q (Pstar A b w θ Q) ∧
        ∀ P : ℝ, IsRetailerOptimal γ A b w θ Q P → P = Pstar A b w θ Q) ∧
      demand A b θ (Pstar A b w θ Q) Q = Real.sqrt ((A - b * w) / 3 * Q ^ θ) ∧
      retailerProfit γ A b w θ Q (Pstar A b w θ Q) =
        (2 / b) * (1 - γ) * ((A - b * w) / 3 * Q ^ θ) ^ (3 / 2 : ℝ)) ∧
    ∀ Q : ℝ, 0 ≤ Q → S A b w θ Q = (2 / b) * ((A - b * w) / 3 * Q ^ θ) ^ (3 / 2 : ℝ) := by sorry

end CoProdBundle.Equil
