-- Prove2me | Theorems.Thm_BetaCoskew_ThreeMoment_Supplement_theorem_1
-- name    : BetaCoskew.ThreeMoment.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:39:25.1358+00:00
-- url     : https://prove2.me/theorems/09c85501-672f-449d-bc3b-f467ee5de4a4
-- title:
--   Theorem 1 (corrected: Stieltjes RDU at atoms) — optimal payoff and positive unit-budget multiplier
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be an atomless probability space, let $\tilde m$ be a measurable, almost surely positive integrable pricing kernel with continuous CDF $F_{\tilde m}$, and let $u,w$ satisfy Assumption 1(ii)–(iii). Use the strict lower quantile, dual weighting $\bar w$, function $N$, least concave majorant $\widehat N$ and its right derivative defined above. Assume, for every $\mu>0$,
--
--   $$
--   \int_0^{1-}(u')^{-1}\bigl(\mu\widehat N'_+(\bar w(p))\bigr)Q^-_{\tilde m}(1-p)\,dp<\infty.
--   $$
--   Then there exists $\lambda^*>0$ such that
--
--   $$
--   X^*=(u')^{-1}\bigl(\lambda^*\widehat N'_+(1-w(F_{\tilde m}(\tilde m)))\bigr),
--   \qquad \mathbb E[\tilde mX^*]=1,
--   $$
--   and $X^*$ maximizes the corrected, genuine Stieltjes RDU value over every measurable, almost surely nonnegative payoff $X$ with $\mathbb E[\tilde mX]=1$. The optimizer is feasible, every feasible payoff has a well-defined extended value, and none has a larger value. No continuous-law condition on payoffs, equilibrium, density or uniqueness of the multiplier is asserted.
--
--   This companion theorem constructs the optimal payoff for (P′). It is independent of the proof of the published Theorem 2. The atomic objective correction is material: the original full-domain claim has the counterexample in DISPROOF.md.
--
--   **Formalization Note** Budget feasibility uses the published Feasible predicate. The objective is the new explicitly corrected Stieltjes objective, rather than the published equilibrium predicate or its restricted competitor class.
--
--   Differences from the source:
--   - correction: the printed objective is ∫u(x)w′(1−F(x))dF(x), also for payoffs with atoms → the objective is the Stieltjes integral against G(x)=1−w(1−F(x)), with jump weights G(x)−G(x−); reason: the full-domain claim is false for the printed objective: on a uniform unit interval take m̃=1+ω, u(x)=√x and w(p)=p²; the prescribed constant payoff has value 0, but the feasible payoff 6ω/5 has value (8/15)√(6/5)>0 (DISPROOF.md); Stieltjes weights preserve probability weighting across jumps and agree with the printed differential expression on continuous laws
--   - encoding: utility on positive wealth and nonnegative feasible payoffs; improper endpoints and possibly infinite utility values are implicit → u(0+) is its extended infimum over positive wealth; signed extended integrals have an explicit measurability and not-both-infinite guard; quantiles are extended at endpoints, real at interior levels; N uses open-interval integrals and slopes use right derivatives; reason: these give genuine endpoint and expectation values without excluding any source payoff, adding smoothness, or assuming a quantile representation
--   - encoding: the kernel is the positive integrable kernel of the finite-asset market, and the problem to solve is (P′) → the probability space, atomlessness, measurable positive integrable kernel, and published utility and weighting assumptions are bound directly, without parameters for assets absent from (P′); reason: every source market supplies these data; conversely any such kernel admits the constant risk-free return 1/E[m̃], so this leaves the payoff problem unchanged
-- source:
--   Shi, Cui & Zhou, Beta and coskewness pricing: perspective from probability weighting, SSRN 3579960 (version of June 2, 2020), p. 10, Theorem 1; pp. 8–9, objective and (2); correction and counterexample in DISPROOF.md

import Mathlib
import Definitions.Def_BetaCoskew_ThreeMoment_Supplement_PayoffProblem

namespace BetaCoskew.ThreeMoment.Supplement

open MeasureTheory ProbabilityTheory

/-- Theorem 1, p.10 (corrected: Stieltjes RDU at atoms).
The conclusion constructs the positive budget multiplier and its optimal
payoff on the entire feasible class of (P′). See DISPROOF.md for the failure
of the printed derivative-times-CDF objective on atomic payoffs. -/
theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (mt : Ω → ℝ)
    (hAtomless : Atomless P) (hmt : Measurable mt)
    (hpos : ∀ᵐ ω ∂P, 0 < mt ω) (hint : Integrable mt P)
    (u w : ℝ → ℝ) (hu : UtilityAssumption u) (hw : WeightingAssumption w)
    (hCDF : Continuous (cdf (P.map mt)))
    (hfinite : AllMuFinite (P.map mt) u w) :
    ∃ lam : ℝ, 0 < lam ∧ IsOptimal P mt u w hw (candidate P mt u w lam) := by sorry

end BetaCoskew.ThreeMoment.Supplement
