-- Prove2me | Theorems.Thm_AlgoTransparency_eq_13
-- name    : AlgoTransparency.eq_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:50:50.314486+00:00
-- url     : https://prove2.me/theorems/9e9b631a-f753-4ca0-8ae6-94aa82460b3c
-- title:
--   Eq. (13): $\Pi_{T3}>\Pi_{O1}$ iff $\beta>\beta_1$
-- statement:
--   With $\Pi_{T3}=\theta(\alpha+\beta)+(1-\theta)\beta-R$, $\Pi_{O1}=\lambda\theta\alpha-(\lambda\theta+(1-\lambda)(1-\theta))R$ and $\beta_1=\lambda\theta(\alpha-R)-(1-\lambda)(1-\theta)R+R-\theta\alpha$,
--
--   $$
--   \Pi_{T3}>\Pi_{O1}\iff\beta>\beta_1 .
--   $$
--
--   In region $C_1$ the agents move from opaque case 1 to transparent case 3, so this is the threshold of the $C_1$ clause of Theorem 1.
--
--   Differences from the source:
--   - generalization: stated under the standing assumptions, in region C1 → for all real parameters; reason: Π_T3 − Π_O1 = β − β1 identically; specializes to the paper's setting
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, §4.3, eq. (13), p.23 (PDF 24)

import Mathlib
import Definitions.Def_AlgoTransparency_beta1

namespace AlgoTransparency

/-- **Eq. (13): the C1 threshold**, Wang, Huang, Jasin & Singh, arXiv:2008.09283v1, §4.3, p.23
(PDF 24).

`Π_T3 > Π_O1` iff `β > β1`, where `Π_T3 = θ(α + β) + (1 − θ)β − R`,
`Π_O1 = λθα − (λθ + (1 − λ)(1 − θ))R` and `β1 = λθ(α − R) − (1 − λ)(1 − θ)R + R − θα`.

**Formalization Note.** Stated for all real parameters: `Π_T3 − Π_O1 = β − β1` identically, so no
assumption is needed. -/
theorem eq_13 (p : Params) :
    p.lam * p.θ * p.α - (p.lam * p.θ + (1 - p.lam) * (1 - p.θ)) * p.R <
        p.θ * (p.α + p.β) + (1 - p.θ) * p.β - p.R ↔
      beta1 p < p.β := by sorry

end AlgoTransparency
