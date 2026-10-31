-- Prove2me | Theorems.Thm_DebtDoubleMarg_discount_firstPassage
-- name    : DebtDoubleMarg.discount_firstPassage
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:39:51.893913+00:00
-- url     : https://prove2.me/theorems/82050e42-6802-40b6-96ba-ca26ac8a8f0a
-- title:
--   First-passage Laplace transform of a gBm from below: $\mathbb E[e^{-r\tilde\tau(\tilde X;X)}]=(X/\tilde X)^{\beta_1}$
-- statement:
--   Let $W$ be a standard Brownian motion, $\sigma>0$, $r>0$, $\mu\in\mathbb R$, and let $x^X$ be the geometric Brownian motion with drift $\mu$ and volatility $\sigma$ started at $X$. For $0<X\le\tilde X$,
--   $$\mathbb E\big[e^{-r\tilde\tau(\tilde X;X)}\big]=\Big(\frac{X}{\tilde X}\Big)^{\beta_1},$$
--   where $\tilde\tau(\tilde X;X)=\inf\{t\ge0: x^X(t)\ge\tilde X\}$, the discount factor is $0$ on $\{\tilde\tau=\infty\}$, and $\beta_1$ is the larger root of $\tfrac12\sigma^2\beta^2+(\mu-\tfrac12\sigma^2)\beta-r=0$.
--
--   This is the identity behind every expectation $\mathbb E_0\{e^{-r\tilde\tau(X_F;x(0))}\cdots\}$ of the timing problems (2), $V_F$ and $V_D$, and behind the factor $(X/X_F)^{\beta_1}$ of the welfare formula (5). It is a step of the proof of Proposition 1, not a numbered result of the paper.
--
--   **Formalization Note** The identity holds for every drift, including $\mu<\sigma^2/2$, where $\tilde\tau=\infty$ with positive probability.
--
--   Differences from the source:
--   - generalization: the standing assumptions of §2 (η > 0, r > µ, δ > 0) → only σ > 0 and r > 0; µ arbitrary; reason: the identity is a property of the geometric Brownian motion alone; under the standing assumptions it is the paper's factor
--   - encoding: dx(t) = µx(t)dt + σx(t)dω(t), x(0) = X (p.4) → x(t) = X·exp((µ − σ²/2)t + σW_t) for a Mathlib Brownian motion W (IsBrownianReal), on any probability space; reason: the unique strong solution of the SDE; the statement holds for every probability space carrying a Brownian motion
--   - encoding: e^{−rτ̃} with τ̃ = inf{t ≥ 0 | x(t) ≥ X̃} (p.6) → τ̃ ∈ [0, ∞] pathwise, and the discount factor is 0 on {τ̃ = ∞}; reason: e^{−r·∞} = 0 for r > 0
-- source:
--   Huberts, Wen, Dawid, Huisman, Kort, Double Marginalization Because of External Financing: Capacity Investment Under Uncertainty, Management Science (2025), doi:10.1287/mnsc.2023.01152, §2.3 p.6 (definition of τ̃ and the factor of (2)); (5) p.6 (factor (X/X_F)^β₁). Proof step of Proposition 1

import Mathlib
import Definitions.Def_DebtDoubleMarg_GeometricBM

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DebtDoubleMarg

/-- **Laplace transform of the first passage of a gBm from below.** For a standard Brownian
motion `W`, `σ > 0`, `r > 0` and `0 < X ≤ X̃`,
`E[e^{−r τ̃(X̃; X)}] = (X / X̃)^{β₁}`, with `e^{−r·∞} = 0` on `{τ̃ = ∞}`.

Huberts et al., *Double Marginalization Because of External Financing*, Management Science
(2025), doi:10.1287/mnsc.2023.01152, §2.3, p.6 (definition of `τ̃`, the factor of (2), `V_F`,
`V_D`) and the factor `(X/X_F)^{β₁}` of (5), p.6. A proof step of Proposition 1, not a numbered
result of the paper.

**Formalization Note** The identity holds for every drift `µ`, including `µ < σ²/2`, where
`P(τ̃ = ∞) > 0`: those paths contribute `0`. -/
theorem discount_firstPassage (μ σ r : ℝ) (hσ : 0 < σ) (hr : 0 < r)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBrownianReal W P) (X Xt : ℝ) (hX : 0 < X) (hXXt : X ≤ Xt) :
    expectedPassageDiscount μ σ r P W Xt X = (X / Xt) ^ beta1 μ σ r := by sorry

end DebtDoubleMarg
