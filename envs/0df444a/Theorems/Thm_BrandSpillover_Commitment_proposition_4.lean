-- Prove2me | Theorems.Thm_BrandSpillover_Commitment_proposition_4
-- name    : BrandSpillover.Commitment.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:57.529679+00:00
-- url     : https://prove2.me/theorems/09da1a35-618f-415c-b6c7-9c0a79d4a3ed
-- title:
--   Proposition 4, p. 19 — Firm W should commit to not using brand spillover iff the no-commitment structure is (O, I) or c < θ − 1/2 − α + αθ
-- statement:
--   Assume the standing assumptions $c > 0$, $\underline\theta \le \theta < 1$, $0 \le \alpha \le 1$, and $\alpha > 0$. Let $(s, w)$ be an equilibrium outcome when Firm W does not commit (brand spillover at level $\alpha$ under $(O,O)$), and $(s_0, w_0)$ an equilibrium outcome when Firm W commits to not using brand spillover (level $0$). Write $\Pi_W$ and $\Pi^{0}_W$ for Firm W's profits at these outcomes. Then:
--
--   1. if $s = (O,I)$, committing is weakly better: $\Pi_W \le \Pi^0_W$;
--   2. if $s \ne (O,I)$, committing is strictly better exactly under condition (ii):
--   $$\Pi_W < \Pi^0_W \iff c < \theta - \tfrac12 - \alpha + \alpha\theta;$$
--   3. condition (ii) is equivalent to $\alpha < \dfrac{2\theta - 1 - 2c}{2(1-\theta)}$.
--
--   This is the paper's answer to whether a weak-brand firm should use brand spillover: committing not to use it pays when the supplier would otherwise drop it, or when the insourcing cost is low relative to the spillover's effect.
--
--   **Formalization Note** "Should commit" is the comparison of Firm W's equilibrium profits with and without commitment, as in the paper's proof. In case (i) the comparison is weak: the paper's proof notes that committing has no effect on Firm W's profit when $c \le \tfrac12(2\theta-1)$. Ties in the CM's choice of structure are allowed, and the statement covers every equilibrium selection. The assumption $\alpha > 0$ is the paper's (p. 17: "the equilibrium outcome when Firm W does not make any commitment is given by Proposition 3 with $\alpha > 0$").
-- source:
--   Wu, Zhang & Zhou, Brand Spillover as a Marketing Strategy, SSRN preprint 3891915 (June 2021), p. 19, Proposition 4 (proof App. A, p. 34)

import Mathlib
import Definitions.Def_BrandSpillover_Commitment_Model

namespace BrandSpillover.Commitment

/-- Proposition 4, p. 19: Firm W should commit to not using brand spillover if and only if (i) the
equilibrium sourcing structure without commitment is `(O, I)`, or (ii)
`c < θ − 1/2 − α + αθ` (equivalently, `α < (2θ − 1 − 2c)/(2(1 − θ))`). Firm W's profit at an
equilibrium without commitment (spillover `α`) is compared with its profit at an equilibrium with
commitment (spillover `0`): under (i) committing is weakly better; otherwise committing is strictly
better exactly when (ii) holds. -/
theorem proposition_4 (P : Params) (hP : P.Standing) (hα : 0 < P.α)
    (s : Structure) (w : ℝ × ℝ) (hs : IsEquilibrium P P.α s w)
    (s₀ : Structure) (w₀ : ℝ × ℝ) (hs₀ : IsEquilibrium P 0 s₀ w₀) :
    (s = .OI → profitW P P.α s w ≤ profitW P 0 s₀ w₀) ∧
    (s ≠ .OI → (profitW P P.α s w < profitW P 0 s₀ w₀ ↔
      P.c < P.θ - 1 / 2 - P.α + P.α * P.θ)) ∧
    (P.c < P.θ - 1 / 2 - P.α + P.α * P.θ ↔
      P.α < (2 * P.θ - 1 - 2 * P.c) / (2 * (1 - P.θ))) := by sorry

end BrandSpillover.Commitment
