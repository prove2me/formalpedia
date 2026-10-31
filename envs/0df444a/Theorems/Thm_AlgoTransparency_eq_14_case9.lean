-- Prove2me | Theorems.Thm_AlgoTransparency_eq_14_case9
-- name    : AlgoTransparency.eq_14_case9
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:50:35.203227+00:00
-- url     : https://prove2.me/theorems/4f577a07-15df-4612-b99e-cf33811611a6
-- title:
--   Eq. (14) for the selected outcome (corrected: the $C_2$ outcome is case 9, payoff $\Pi_{O9}$, not case 4; the threshold $\beta_2$ is unchanged)
-- statement:
--   Assume the standing assumptions. Then
--
--   1. $R(2\lambda-1)(\alpha+\beta-R)-\alpha\beta\lambda^2>0$;
--   2. with
--   $$
--   \Pi_{O9}=\frac{(R-\beta)(2\lambda-1)(\alpha+\beta-R)\big(\lambda\theta(\alpha-R)-(1-\theta)(1-\lambda)R\big)}{R(2\lambda-1)(\alpha+\beta-R)-\alpha\beta\lambda^2},
--   $$
--   the firm's payoff at the selected (case 9) opaque outcome on $C_2'$, $\Pi_{T3}=\theta(\alpha+\beta)+(1-\theta)\beta-R$ and $\beta_2=R-\dfrac{\alpha R(1-\lambda)}{(\alpha-R)\lambda+R(1-\lambda)}$,
--   $$
--   \Pi_{T3}>\Pi_{O9}\iff\beta>\beta_2 .
--   $$
--
--   This is the threshold of the $C_2$ clause of Theorem 1; the paper's threshold survives the correction of the outcome.
--
--   Differences from the source:
--   - correction: Π_T3 > Π_O4 iff β > β2, with the case-4 payoff Π_O4 = θ(α + β − R)(1 − R(1 − θ)(1 − λ)/((α − R)θλ)) → Π_T3 > Π_O9 iff β > β2, with the case-9 payoff Π_O9, together with the positivity of Π_O9's denominator; reason: case 4 is never the selected outcome (lemma_1; counterexample at λ = 4/5, R = 1, (C_H, C_L) = (3/10, 3/5)); the selected outcome on C2' is case 9
--   - reading: θ and 1 − θ are "portions"; 0 < θ < 1 is never written → Standing includes 0 < θ < 1; reason: the paper divides by θ and 1 − θ
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, §4.3, eq. (14), p.23 (PDF 24)

import Mathlib
import Definitions.Def_AlgoTransparency_Standing
import Definitions.Def_AlgoTransparency_beta2

namespace AlgoTransparency

/-- **Eq. (14) for the selected outcome (corrected): the C2 threshold**, Wang, Huang, Jasin &
Singh, arXiv:2008.09283v1, §4.3, p.23 (PDF 24).

Under the standing assumptions:

1. the denominator `R(2λ − 1)(α + β − R) − αβλ²` of `Π_O9` is positive;
2. `Π_T3 > Π_O9` iff `β > β2`, where `Π_T3 = θ(α + β) + (1 − θ)β − R`,
   `Π_O9 = (R − β)(2λ − 1)(α + β − R)(λθ(α − R) − (1 − θ)(1 − λ)R) / (R(2λ − 1)(α + β − R) − αβλ²)`
   is the firm's payoff at the selected (both-types-mixing, case 9) opaque outcome on `C2'`
   (see `lemma_1`), and `β2 = R − αR(1 − λ)/((α − R)λ + R(1 − λ))`.

**Formalization Note.** The printed (14) compares `Π_T3` with the case-4 payoff
`Π_O4 = θ(α + β − R)(1 − R(1 − θ)(1 − λ)/((α − R)θλ))`; that comparison is correct algebra, but
case 4 is never the selected outcome (`lemma_1`), so the milestone compares with `Π_O9`. The
threshold is the same `β2`. -/
theorem eq_14_case9 (p : Params) (hp : Standing p) :
    0 < p.R * (2 * p.lam - 1) * (p.α + p.β - p.R) - p.α * p.β * p.lam ^ 2 ∧
    ((p.R - p.β) * (2 * p.lam - 1) * (p.α + p.β - p.R) *
          (p.lam * p.θ * (p.α - p.R) - (1 - p.θ) * (1 - p.lam) * p.R) /
        (p.R * (2 * p.lam - 1) * (p.α + p.β - p.R) - p.α * p.β * p.lam ^ 2) <
        p.θ * (p.α + p.β) + (1 - p.θ) * p.β - p.R ↔
      beta2 p < p.β) := by sorry

end AlgoTransparency
