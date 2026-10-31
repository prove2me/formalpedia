-- Prove2me | Theorems.Thm_AlgoTransparency_eq_15
-- name    : AlgoTransparency.eq_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:51:12.921743+00:00
-- url     : https://prove2.me/theorems/a4fd328f-0d26-46ab-958c-b364ce0a896c
-- title:
--   Eq. (15) and $\beta_3=\bar\beta$: transparency never pays in $C_3$
-- statement:
--   Assume the standing assumptions, and let $\Pi_{T3}=\theta(\alpha+\beta)+(1-\theta)\beta-R$ and $\Pi_{O5}=\frac{2\lambda-1}{\lambda}\theta(\alpha+\beta-R)$. Then
--
--   1. $\Pi_{T3}>\Pi_{O5}\iff\beta>\beta_3$, where $\beta_3=\dfrac{\lambda\theta\alpha-\theta\alpha-2\lambda\theta R+\theta R+\lambda R}{\lambda-2\theta\lambda+\theta}$;
--   2. $\beta_3=\bar\beta$, the upper bound of Assumption 3;
--   3. hence $\Pi_{T3}<\Pi_{O5}$.
--
--   In region $C_3$ the agents move from opaque case 5 to transparent case 3, and Assumption 3 keeps $\beta$ below the threshold.
--
--   Differences from the source:
--   - generalization: "the firm will never prefer to be transparent in this region" (Π_T3 ≤ Π_O5) → Π_T3 < Π_O5; reason: Assumption 3 is strict, β < β̄ = β3; the strict inequality implies the paper's
--   - reading: θ and 1 − θ are "portions"; 0 < θ < 1 is never written → Standing includes 0 < θ < 1; reason: the paper divides by θ and 1 − θ
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, §4.3, eq. (15), p.23 (PDF 24)

import Mathlib
import Definitions.Def_AlgoTransparency_Standing
import Definitions.Def_AlgoTransparency_beta3
import Definitions.Def_AlgoTransparency_betaBar

namespace AlgoTransparency

/-- **Eq. (15) and `β3 = β̄`: the C3 comparison**, Wang, Huang, Jasin & Singh,
arXiv:2008.09283v1, §4.3, p.23 (PDF 24).

Under the standing assumptions, with `Π_T3 = θ(α + β) + (1 − θ)β − R` and
`Π_O5 = ((2λ − 1)/λ) θ(α + β − R)`:

1. `Π_T3 > Π_O5` iff `β > β3 = (λθα − θα − 2λθR + θR + λR)/(λ − 2θλ + θ)`;
2. `β3 = β̄`, the upper bound of Assumption 3;
3. hence `Π_T3 < Π_O5`: the firm never prefers transparency in region C3.

**Formalization Note.** Clause 3 is the paper's conclusion "the firm will never prefer to be
transparent in this region", drawn from clauses 1–2 and `β < β̄`; it is stated as the strict
inequality the argument gives. -/
theorem eq_15 (p : Params) (hp : Standing p) :
    ((2 * p.lam - 1) / p.lam * p.θ * (p.α + p.β - p.R) <
        p.θ * (p.α + p.β) + (1 - p.θ) * p.β - p.R ↔ beta3 p < p.β) ∧
    beta3 p = betaBar p ∧
    p.θ * (p.α + p.β) + (1 - p.θ) * p.β - p.R <
      (2 * p.lam - 1) / p.lam * p.θ * (p.α + p.β - p.R) := by sorry

end AlgoTransparency
