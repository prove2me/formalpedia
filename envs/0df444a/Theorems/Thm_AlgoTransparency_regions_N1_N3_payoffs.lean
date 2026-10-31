-- Prove2me | Theorems.Thm_AlgoTransparency_regions_N1_N3_payoffs
-- name    : AlgoTransparency.regions_N1_N3_payoffs
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:50:05.994321+00:00
-- url     : https://prove2.me/theorems/ea9b06b5-f732-4a65-9ef9-b5d771a4950c
-- title:
--   §4.3, pp.21–22: payoff comparisons in regions $N_1$–$N_3$
-- statement:
--   Assume the standing assumptions and write
--   $\Pi_{O1}=\lambda\theta\alpha-(\lambda\theta+(1-\lambda)(1-\theta))R$, $\Pi_{O2}=\theta(\alpha+\beta)-\theta R$, $\Pi_{O3}=\lambda\theta(\alpha+\beta)+(1-\lambda)(1-\theta)\beta-(\lambda\theta+(1-\lambda)(1-\theta))R$, $\Pi_{T1}=0$, $\Pi_{T2}=\theta(\alpha+\beta-R)$ and $\Pi_{T3}=\theta(\alpha+\beta)+(1-\theta)\beta-R$. Then:
--
--   1. ($N_1$) $\Pi_{O1}>\Pi_{T1}=0$;
--   2. ($N_2$) $\Pi_{O2}=\Pi_{T2}$;
--   3. ($N_3$)
--   $$
--   \Pi_{T3}-\Pi_{O3}=(1-\lambda)\theta(\alpha+\beta-R)-\lambda(1-\theta)(R-\beta)=\theta(1-\lambda)\alpha-\big(\theta(1-\lambda)+(1-\theta)\lambda\big)(R-\beta)<0 .
--   $$
--
--   Where the same case is played in both games, transparency only destroys the information carried by the correlational feature.
--
--   Differences from the source:
--   - reading: the bullets compare the firm's payoffs in regions N1–N3 → the payoff formulas of Lemmas 1–2 compared as real expressions under the standing assumptions; reason: the bullets' mathematical content; which case is played in which region is lemma_1 and lemma_2
--   - reading: θ and 1 − θ are "portions"; 0 < θ < 1 is never written → Standing includes 0 < θ < 1; reason: the paper divides by θ and 1 − θ
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, §4.3, pp.21–22 (PDF 22–23)

import Mathlib
import Definitions.Def_AlgoTransparency_Standing

namespace AlgoTransparency

/-- **The payoff comparisons in regions N1–N3**, Wang, Huang, Jasin & Singh, arXiv:2008.09283v1,
§4.3, pp.21–22 (PDF 22–23).

Under the standing assumptions, with `Π_O1 = λθα − (λθ + (1 − λ)(1 − θ))R`,
`Π_O2 = θ(α + β) − θR`, `Π_O3 = λθ(α + β) + (1 − λ)(1 − θ)β − (λθ + (1 − λ)(1 − θ))R`,
`Π_T1 = 0`, `Π_T2 = θ(α + β − R)` and `Π_T3 = θ(α + β) + (1 − θ)β − R`:

1. (N1) `Π_O1 > Π_T1 = 0`;
2. (N2) `Π_O2 = Π_T2`;
3. (N3) `Π_T3 − Π_O3 = (1 − λ)θ(α + β − R) − λ(1 − θ)(R − β)
   = θ(1 − λ)α − (θ(1 − λ) + (1 − θ)λ)(R − β) < 0`.

**Formalization Note.** These are the payoff formulas of Lemmas 1 and 2 compared as real
expressions; which equilibrium is selected in which region is the content of `lemma_1` and
`lemma_2`. -/
theorem regions_N1_N3_payoffs (p : Params) (hp : Standing p) :
    0 < p.lam * p.θ * p.α - (p.lam * p.θ + (1 - p.lam) * (1 - p.θ)) * p.R ∧
    p.θ * (p.α + p.β) - p.θ * p.R = p.θ * (p.α + p.β - p.R) ∧
    (p.θ * (p.α + p.β) + (1 - p.θ) * p.β - p.R) -
        (p.lam * p.θ * (p.α + p.β) + (1 - p.lam) * (1 - p.θ) * p.β -
          (p.lam * p.θ + (1 - p.lam) * (1 - p.θ)) * p.R) =
      (1 - p.lam) * p.θ * (p.α + p.β - p.R) - p.lam * (1 - p.θ) * (p.R - p.β) ∧
    (1 - p.lam) * p.θ * (p.α + p.β - p.R) - p.lam * (1 - p.θ) * (p.R - p.β) =
      p.θ * (1 - p.lam) * p.α - (p.θ * (1 - p.lam) + (1 - p.θ) * p.lam) * (p.R - p.β) ∧
    p.θ * (1 - p.lam) * p.α - (p.θ * (1 - p.lam) + (1 - p.θ) * p.lam) * (p.R - p.β) < 0 := by sorry

end AlgoTransparency
