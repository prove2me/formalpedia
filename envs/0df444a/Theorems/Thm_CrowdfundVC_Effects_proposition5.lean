-- Prove2me | Theorems.Thm_CrowdfundVC_Effects_proposition5
-- name    : CrowdfundVC.Effects.proposition5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:38.094799+00:00
-- url     : https://prove2.me/theorems/5bdbca9d-c081-464f-8c3c-2d11490999cc
-- title:
--   Proposition 5, PDF p. 19 — the startup's value of waiting Δa decreases in p2
-- statement:
--   Under the standing assumptions ($0 \le R_f < R_0 < R_s$, $0 < K < R_0$, $0 \le \rho \le 1$, $0 \le \beta \le 1$, $0 \le p_2 \le p_1 \le 1$, $0 \le p_a \le 1$, $\tilde e_1|S \ge R_0$), let $q$ satisfy $p_2 \le q \le p_1$, and let $\Delta_a(q)$ denote the startup's value of waiting $\Delta_a = \tilde\pi_a - \pi_a$ computed with VC$_2$'s prior replaced by $q$, all other parameters unchanged. Then
--   $$\Delta_a(q) \le \Delta_a(p_2).$$
--
--   When the VC firms' beliefs converge, inducing pre-crowdfunding investment becomes cheaper for the startup, so its incentive to induce a delay weakens; by Proposition 4 this moves the optimal share toward $\alpha_0$.
--
--   **Formalization Note** "Decreases" is weak, as for Proposition 3(ii). $0 \le R_f$ is added as for every item.
-- source:
--   Hu, Jin & Keppo, The Crowdfunding Effects on Venture Capital Investment, SSRN author manuscript (abstract 3512638, 2024-03-15; Management Science DOI 10.1287/mnsc.2022.00994), PDF p. 19, Proposition 5; proof Online Appendix D, PDF p. 51 (OA p. 24)

import Mathlib
import Definitions.Def_CrowdfundVC_Effects_Model

namespace CrowdfundVC.Effects

/-- Proposition 5 (p. 19): the startup's value of waiting `Δa` (weakly) decreases in `p2`; raising VC2's
prior from `p2` to `q ≤ p1`, all else fixed, does not increase `Δa`. -/
theorem proposition5 (P : Params)
    (hRf0 : 0 ≤ P.Rf) (hRfR0 : P.Rf < P.R0) (hR0Rs : P.R0 < P.Rs) (hK0 : 0 < P.K)
    (hKR0 : P.K < P.R0) (hρ0 : 0 ≤ P.ρ) (hρ1 : P.ρ ≤ 1) (hβ0 : 0 ≤ P.β) (hβ1 : P.β ≤ 1)
    (hp2 : 0 ≤ P.p2) (hp12 : P.p2 ≤ P.p1) (hp1 : P.p1 ≤ 1) (hpa0 : 0 ≤ P.pa) (hpa1 : P.pa ≤ 1)
    (hI : P.R0 ≤ e1S P) :
    ∀ q : ℝ, P.p2 ≤ q → q ≤ P.p1 → deltaA { P with p2 := q } ≤ deltaA P := by sorry

end CrowdfundVC.Effects
