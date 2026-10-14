-- Prove2me | Theorems.Thm_CrowdfundVC_Effects_proposition3_ii
-- name    : CrowdfundVC.Effects.proposition3_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:56.53705+00:00
-- url     : https://prove2.me/theorems/00a52e3b-9094-4fc6-a818-31a98ab6c681
-- title:
--   Proposition 3(ii), PDF p. 16 — α0 decreases in p2
-- statement:
--   Under the standing assumptions ($0 \le R_f < R_0 < R_s$, $0 < K < R_0$, $0 \le \rho \le 1$, $0 \le \beta \le 1$, $0 \le p_2 \le p_1 \le 1$, $0 \le p_a \le 1$, $\tilde e_1|S \ge R_0$), let $q$ satisfy $p_2 \le q \le p_1$, and let $\alpha_0(q)$ denote the threshold of Proposition 2 computed with VC$_2$'s prior replaced by $q$, all other parameters unchanged. Then
--   $$\alpha_0(q) \le \alpha_0(p_2).$$
--
--   When VC$_2$'s belief moves toward VC$_1$'s, VC$_2$ becomes a stronger outside option after crowdfunding, waiting becomes less attractive for VC$_1$, and the share needed for pre-crowdfunding investment falls.
--
--   **Formalization Note** "Decreases" is weak: on the branch $\alpha_0 = T_2$ the threshold does not depend on $p_2$ (Figure 1). $0 \le R_f$ is added as for every item.
-- source:
--   Hu, Jin & Keppo, The Crowdfunding Effects on Venture Capital Investment, SSRN author manuscript (abstract 3512638, 2024-03-15; Management Science DOI 10.1287/mnsc.2022.00994), PDF p. 16, Proposition 3(ii); proof Online Appendix D, PDF pp. 50–51 (OA pp. 23–24)

import Mathlib
import Definitions.Def_CrowdfundVC_Effects_Model

namespace CrowdfundVC.Effects

/-- Proposition 3(ii) (p. 16): `α0` (weakly) decreases in `p2`; raising VC2's prior from `p2` to
`q ≤ p1`, all else fixed, does not increase `α0`. -/
theorem proposition3_ii (P : Params)
    (hRf0 : 0 ≤ P.Rf) (hRfR0 : P.Rf < P.R0) (hR0Rs : P.R0 < P.Rs) (hK0 : 0 < P.K)
    (hKR0 : P.K < P.R0) (hρ0 : 0 ≤ P.ρ) (hρ1 : P.ρ ≤ 1) (hβ0 : 0 ≤ P.β) (hβ1 : P.β ≤ 1)
    (hp2 : 0 ≤ P.p2) (hp12 : P.p2 ≤ P.p1) (hp1 : P.p1 ≤ 1) (hpa0 : 0 ≤ P.pa) (hpa1 : P.pa ≤ 1)
    (hI : P.R0 ≤ e1S P) :
    ∀ q : ℝ, P.p2 ≤ q → q ≤ P.p1 → alpha0 { P with p2 := q } ≤ alpha0 P := by sorry

end CrowdfundVC.Effects
