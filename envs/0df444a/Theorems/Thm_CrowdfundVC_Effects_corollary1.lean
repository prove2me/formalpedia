-- Prove2me | Theorems.Thm_CrowdfundVC_Effects_corollary1
-- name    : CrowdfundVC.Effects.corollary1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:37.685912+00:00
-- url     : https://prove2.me/theorems/84a3c187-f998-4bde-93da-8da9fb0c7e99
-- title:
--   Corollary 1, PDF p. 15 — α0 ≥ R0/ẽ1|S
-- statement:
--   Under the standing assumptions ($0 \le R_f < R_0 < R_s$, $0 < K < R_0$, $0 \le \rho \le 1$, $0 \le \beta \le 1$, $0 \le p_2 \le p_1 \le 1$, $0 \le p_a \le 1$, $\tilde e_1|S \ge R_0$), the threshold $\alpha_0$ of Proposition 2 satisfies
--   $$\alpha_0 \ge \frac{R_0}{\tilde e_1|S}.$$
--
--   The minimum share that induces pre-crowdfunding investment is at least the minimum share that induces investment after a successful campaign, even before the reduction of the share to $\alpha'$ is taken into account. This is what makes the second indicator of the startup's objective (§5.2) a nonempty range.
--
--   **Formalization Note** $0 \le R_f$ is added as for every item.
-- source:
--   Hu, Jin & Keppo, The Crowdfunding Effects on Venture Capital Investment, SSRN author manuscript (abstract 3512638, 2024-03-15; Management Science DOI 10.1287/mnsc.2022.00994), PDF p. 15, Corollary 1; proof Online Appendix D, PDF p. 50 (OA p. 23)

import Mathlib
import Definitions.Def_CrowdfundVC_Effects_Model

namespace CrowdfundVC.Effects

/-- Corollary 1 (p. 15): `α0 ≥ R0/ẽ1|S`. -/
theorem corollary1 (P : Params)
    (hRf0 : 0 ≤ P.Rf) (hRfR0 : P.Rf < P.R0) (hR0Rs : P.R0 < P.Rs) (hK0 : 0 < P.K)
    (hKR0 : P.K < P.R0) (hρ0 : 0 ≤ P.ρ) (hρ1 : P.ρ ≤ 1) (hβ0 : 0 ≤ P.β) (hβ1 : P.β ≤ 1)
    (hp2 : 0 ≤ P.p2) (hp12 : P.p2 ≤ P.p1) (hp1 : P.p1 ≤ 1) (hpa0 : 0 ≤ P.pa) (hpa1 : P.pa ≤ 1)
    (hI : P.R0 ≤ e1S P) :
    P.R0 / e1S P ≤ alpha0 P := by sorry

end CrowdfundVC.Effects
