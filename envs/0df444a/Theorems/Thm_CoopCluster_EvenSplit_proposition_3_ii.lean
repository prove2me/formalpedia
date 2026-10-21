-- Prove2me | Theorems.Thm_CoopCluster_EvenSplit_proposition_3_ii
-- name    : CoopCluster.EvenSplit.proposition_3_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:16.045681+00:00
-- url     : https://prove2.me/theorems/6294ece8-65a2-4d36-aed1-4f0be8e18bca
-- title:
--   Proposition 3(ii), at t = 0, p. 113 (PDF 8) — equilibrium arrival rate, profit, utilization, and cost share 1/2
-- statement:
--   Consider the co-opetition game of §4 with an even cost split ($t=0$), under the standing assumptions and $\theta\ge 0$. Let $(P^O,\alpha^O)$ be any symmetric equilibrium and $\lambda^O=D(\alpha^O)-\beta_0P^O$ the common arrival rate. Then
--
--   1. $\displaystyle \lambda^O=\frac{(\beta_0+\theta)D(\alpha^O)}{2\beta_0+\theta}$;
--   2. each provider's profit is $\Pi^O=P^O\lambda^O-C(\alpha^O)/2-\gamma/w$;
--   3. each provider's utilization is
--   $$\rho^O=1-\frac{1}{w\lambda^O+1};$$
--   4. each provider's cost share is $\tfrac12$.
--
--   These identities express the equilibrium performance in closed form.
--
--   **Formalization Note.** Only $t=0$ is formalized (the page's $t\,\beta_0(\beta_0+2\theta)C(\alpha^O)$ term vanishes). At $t=0$ the cost-share clause holds by definition, and the profit identity is algebra once the share is $\tfrac12$; the content is in item 1 and in item 3, which needs $w\lambda^O+1\ne 0$.
-- source:
--   Yuan, Dai, Chen & Gavirneni, Co-opetition in service clusters with waiting-area entertainment, MSOM 23(1):106–122 (2021), p. 113 (PDF 8), Proposition 3(ii), specialised to t = 0

import Mathlib
import Definitions.Def_CoopCluster_EvenSplit_Model

namespace CoopCluster.EvenSplit

theorem proposition_3_ii (M : Params) (hS : M.Standing) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∀ P α : ℝ, IsSymEq M θ 0 P α →
      arrival M θ α P P = (M.b0 + θ) * D M α / (2 * M.b0 + θ) ∧
      firmProfit M θ 0 α P P = P * arrival M θ α P P - entCost M α / 2 - M.γ / M.w ∧
      utilization M (arrival M θ α P P) = 1 - 1 / (M.w * arrival M θ α P P + 1) ∧
      costShare 0 (arrival M θ α P P) (arrival M θ α P P) = 1 / 2 := by sorry

end CoopCluster.EvenSplit
