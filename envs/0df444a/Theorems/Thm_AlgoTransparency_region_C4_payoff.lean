-- Prove2me | Theorems.Thm_AlgoTransparency_region_C4_payoff
-- name    : AlgoTransparency.region_C4_payoff
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:51:24.889075+00:00
-- url     : https://prove2.me/theorems/b39f3360-a282-48b8-a3ba-e4cdbc6a50ef
-- title:
--   §4.3, p.23: $\Pi_{T2}>\Pi_{O1}$ regardless of $\beta$ (region $C_4$)
-- statement:
--   Under the standing assumptions,
--
--   $$
--   \Pi_{T2}=\theta(\alpha+\beta-R)>\lambda\theta\alpha-(\lambda\theta+(1-\lambda)(1-\theta))R=\Pi_{O1}.
--   $$
--
--   In region $C_4$ the agents move from opaque pooling (case 1) to transparent separation (case 2), and the firm gains for every admissible $\beta$.
--
--   Differences from the source:
--   - reading: "regardless of β" → for every β allowed by the standing assumptions; reason: β is constrained by Assumptions 1 and 3 throughout the paper
--   - reading: θ and 1 − θ are "portions"; 0 < θ < 1 is never written → Standing includes 0 < θ < 1; reason: the paper divides by θ and 1 − θ
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, §4.3, p.23 (PDF 24)

import Mathlib
import Definitions.Def_AlgoTransparency_Standing

namespace AlgoTransparency

/-- **The payoff comparison in region C4**, Wang, Huang, Jasin & Singh, arXiv:2008.09283v1,
§4.3, p.23 (PDF 24).

Under the standing assumptions, `Π_T2 > Π_O1` for every admissible `β`, where
`Π_T2 = θ(α + β − R)` and `Π_O1 = λθα − (λθ + (1 − λ)(1 − θ))R`.

**Formalization Note.** "Regardless of β" is read as: for every `β` allowed by the standing
assumptions. -/
theorem region_C4_payoff (p : Params) (hp : Standing p) :
    p.lam * p.θ * p.α - (p.lam * p.θ + (1 - p.lam) * (1 - p.θ)) * p.R <
      p.θ * (p.α + p.β - p.R) := by sorry

end AlgoTransparency
