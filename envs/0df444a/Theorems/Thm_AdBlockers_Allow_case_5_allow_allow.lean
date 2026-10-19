-- Prove2me | Theorems.Thm_AdBlockers_Allow_case_5_allow_allow
-- name    : AdBlockers.Allow.case_5_allow_allow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:16:34.843479+00:00
-- url     : https://prove2.me/theorems/80a81bb5-5d2e-4cd7-821d-9eea96d6cad4
-- title:
--   Proof of Proposition 1, case 5 — (Allow, Allow): a₁ = a₂ = 1/β is the unique stage-2 equilibrium, profit λ/(2β) each
-- statement:
--   Let $\lambda, \beta > 0$ (and $\mu, \gamma$ arbitrary) and suppose both platforms Allow ad blockers. Adblock users then see no ads and pay nothing, so only the non-adblock segment of mass $\lambda$ generates revenue. Then $a_1 = a_2 = 1/\beta$ is a stage-2 equilibrium, each platform earns
--   $$
--   r_1 = r_2 = \frac{\lambda}{2\beta},
--   $$
--   and every stage-2 equilibrium $(a_1, a_2)$ of this subgame has $a_1 = a_2 = 1/\beta$.
--
--   This is the on-path subgame of the (Allow, Allow) equilibrium of Proposition 1.
-- source:
--   Despotakis, Ravi & Srinivasan, The Beneficial Effects of Ad Blockers, SSRN 3083119 (version of Nov. 28, 2017), p. 42, proof of Proposition 1 (Appendix A.1), case 5

import Mathlib
import Definitions.Def_AdBlockers_Allow_Model

namespace AdBlockers.Allow

/-- Proof of Proposition 1 (Appendix A.1), case 5, p. 42 (both platforms Allow ad blockers):
`a₁ = a₂ = 1/β` is a stage-2 equilibrium of the (Allow, Allow) subgame, each platform earns
`λ/(2β)`, and it is the only stage-2 equilibrium of that subgame. -/
theorem case_5_allow_allow (lam μ β γ : ℝ) (hlam : 0 < lam) (hβ : 0 < β) :
    IsStage2NE lam μ β γ .allow .allow (1 / β) (1 / β) ∧
      rev₁ lam μ β γ .allow .allow (1 / β) (1 / β) = lam / (2 * β) ∧
      rev₂ lam μ β γ .allow .allow (1 / β) (1 / β) = lam / (2 * β) ∧
      ∀ a₁ a₂ : ℝ, IsStage2NE lam μ β γ .allow .allow a₁ a₂ → a₁ = 1 / β ∧ a₂ = 1 / β := by sorry

end AdBlockers.Allow
