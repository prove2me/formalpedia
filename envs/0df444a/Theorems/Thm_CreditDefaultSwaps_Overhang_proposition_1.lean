-- Prove2me | Theorems.Thm_CreditDefaultSwaps_Overhang_proposition_1
-- name    : CreditDefaultSwaps.Overhang.proposition_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:05:05.883989+00:00
-- url     : https://prove2.me/theorems/724efc1c-4113-4c52-9588-afdf9a3399b5
-- title:
--   Proposition 1 — CDS protection strictly raises bankruptcy and investment thresholds
-- statement:
--   Fix the coupon and every primitive of the post-initiation model on a complete, usual filtered risk-neutral Brownian probability space. Assume $r,\sigma,\Pi,i>0$, $\varphi,C\ge0$, $r>\mu+i$, $\tau,\alpha\in[0,1]$, $0\le\eta<1$, and $U_i>U_0$ as defined in the model. Let $0\le\theta_L<\theta_H\le1$. For any globally optimal threshold policies at the two positions, with thresholds $(x_{d,L},x_{i,L},x_{n,L})$ and $(x_{d,H},x_{i,H},x_{n,H})$,
--   $$x_{d,L}<x_{d,H}\quad\text{and}\quad x_{i,L}<x_{i,H}.$$
--   Optimality means maximizing actual expected discounted dividends over admissible adapted investment, workout and bankruptcy decisions whose negotiated transfers satisfy the individually rational Nash split. A threshold policy has an optimal controlled realization at every positive initial productivity. The coupon is fixed, not reoptimized with protection. The protection leg retains its positive part, and the tax shield is suspended in workouts. Never defaulting, zero thresholds, and the zero-bargaining-weight endpoint remain in the domain. Both conclusions are strict, as in the printed proof; source proof findings are recorded separately and are not added as hypotheses.
--
--   Differences from the source:
--   - reading: equation (9) uses (1−τ)(Πx−s) across regimes → firm cash flow minus service, with the coupon tax shield suspended during workouts; reason: the explicit model in §2 and Appendix A.2 fixes the tax regime; see I3
--   - encoding: continuous-time filtered Brownian dynamics and admissible decisions → a continuous Brownian version, progressive controls, the stochastic exponential, and nonnegative extended stopping times; reason: standard nonanticipating controls and never-default outcomes are represented without discretization
--   - encoding: finite discounted cash-flow values and Nash renegotiation → integrable actual payments and conditional continuation values satisfying the individually rational surplus split; reason: avoids default-valued integrals and the endpoint zero-power ambiguity
--   - encoding: the model’s optimal bankruptcy and investment thresholds → every pair of globally optimal threshold realizations, with stopping priority and investment at the investment boundary; reason: existence is explicit in the optimal-threshold predicate; no chosen roots, assumed ordering across positions, or tie-breaker forces the result
--   - encoding: economic primitives and the non-CDS benchmark → positive rates r, σ, Π and i, nonnegative cost and coupon, 0≤η<1, 0≤α,τ≤1, and zero boundaries allowed; reason: retains all meaningful endpoint cases, including η=0, θ=0, θ=1, zero cost and zero coupon
--   - encoding: §3.1 uses the simplified loss-given-default expression → the positive-part CDS payoff of §2 is retained in both protection and the creditor reservation value; reason: agrees with the simplified formula when liquidation does not exceed face value and preserves the stated cash-settlement contract at every other state
-- source:
--   Wong and Yu, Credit Default Swaps and Debt Overhang, Management Science (2021), DOI 10.1287/mnsc.2020.3953, supplied source.pdf, Proposition 1, printed p. 12 (PDF p. 13); proof Appendix A.2, printed pp. 42–43 (PDF pp. 43–44)

import Definitions.Def_CreditDefaultSwaps_Overhang_Optimality

namespace CreditDefaultSwaps.Overhang

theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω]
    (p : Primitives) (N : Noise Ω) (hp : Standing p)
    (thetaLow thetaHigh : ℝ) (hLow : 0 ≤ thetaLow)
    (hIncrease : thetaLow < thetaHigh) (hHigh : thetaHigh ≤ 1)
    (low high : Thresholds)
    (hOptimalLow : OptimalThresholds p N thetaLow low)
    (hOptimalHigh : OptimalThresholds p N thetaHigh high) :
    low.bankruptcy < high.bankruptcy ∧ low.investment < high.investment := by sorry

end CreditDefaultSwaps.Overhang
