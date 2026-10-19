-- Prove2me | Theorems.Thm_AdBlockers_Allow_case_8_ban_allow
-- name    : AdBlockers.Allow.case_8_ban_allow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:16:33.134445+00:00
-- url     : https://prove2.me/theorems/88d58029-a198-4ce8-bc38-60177494120b
-- title:
--   Proof of Proposition 1, case 8 (corrected) — under the γ/β condition, (Ban, Allow) has a stage-2 equilibrium where the Ban platform earns ≤ λ/(2β)
-- statement:
--   Let $\lambda, \mu, \beta, \gamma > 0$ and suppose
--   $$
--   \frac{\lambda + \mu\cdot\gamma/\beta}{(3\lambda + 4\mu\cdot\gamma/\beta)^2} \;\le\; \frac{\lambda}{(3\lambda + 2\mu)^2}.
--   $$
--   Then the subgame in which platform 1 Bans ad blockers and platform 2 Allows them has a stage-2 equilibrium $(a_1, a_2)$ in which platform 1's revenue satisfies
--   $$
--   r_1 \le \frac{\lambda}{2\beta}.
--   $$
--
--   This is what Proposition 1 needs from case 8: a platform that deviates from (Allow, Allow) to Ban cannot gain.
--
--   **Formalization Note** The paper gives the interior first-order point with platform-1 profit $(3\lambda+2\mu)^2(\beta\lambda+\gamma\mu)/(2(3\beta\lambda+4\gamma\mu)^2)$. For large $\gamma/\beta$ that point is not a stage-2 equilibrium (the Ban platform prefers to give up the adblock segment), so the statement is posed as existence of some stage-2 equilibrium with the required revenue bound.
-- source:
--   Despotakis, Ravi & Srinivasan, The Beneficial Effects of Ad Blockers, SSRN 3083119 (version of Nov. 28, 2017), p. 43, proof of Proposition 1 (Appendix A.1), case 8 (derivation in case 6, pp. 42–43; corrected: existence of a stage-2 equilibrium); condition from p. 44

import Mathlib
import Definitions.Def_AdBlockers_Allow_Model

namespace AdBlockers.Allow

/-- Proof of Proposition 1 (Appendix A.1), case 8, p. 43 (platform 1 Bans, platform 2 Allows),
corrected: whenever `(λ + µ·γ/β)/(3λ + 4µ·γ/β)² ≤ λ/(3λ + 2µ)²`, the (Ban, Allow) subgame has a
stage-2 equilibrium in which the Ban platform earns at most `λ/(2β)`. -/
theorem case_8_ban_allow (lam μ β γ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (hβ : 0 < β) (hγ : 0 < γ)
    (h2 : (lam + μ * (γ / β)) / (3 * lam + 4 * μ * (γ / β)) ^ 2 ≤ lam / (3 * lam + 2 * μ) ^ 2) :
    ∃ e₁ e₂ : ℝ, IsStage2NE lam μ β γ .ban .allow e₁ e₂ ∧
      rev₁ lam μ β γ .ban .allow e₁ e₂ ≤ lam / (2 * β) := by sorry

end AdBlockers.Allow
