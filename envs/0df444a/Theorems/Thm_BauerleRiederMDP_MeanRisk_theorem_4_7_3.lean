-- Prove2me | Theorems.Thm_BauerleRiederMDP_MeanRisk_theorem_4_7_3
-- name    : BauerleRiederMDP.MeanRisk.theorem_4_7_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:29:12.765015+00:00
-- url     : https://prove2.me/theorems/8c40cfb2-72de-45fa-a878-520d57d45e13
-- title:
--   Theorem 4.7.3 — value and stationary optimal policy of the binomial mean-risk problem (MR)
-- statement:
--   Throughout, the market is the binomial (Cox–Ross–Rubinstein) model of §4.7 with one stock and one bond with interest rate $i=0$: wealth $X_{n+1}=X_n+f_n(X_n)\,R_{n+1}$, where $f_n(x)\in\mathbb R$ is the amount invested in the stock and the relative risks $R_1,\dots,R_N$ are independent with $\mathbb P(R_n=u-1)=p\in(0,1)$, $\mathbb P(R_n=d-1)=1-p$. A policy $\pi=(f_0,\dots,f_{N-1})\in F^N$ is a sequence of measurable decision rules $f_n:\mathbb R\to\mathbb R$, and $X_0=x_0$. Assumption (FM) of the section is in force: (i) $0<d<1<u$ (no arbitrage; $d>0$ is the binomial model of §3.1), (iii) $0<x_0<\mu$, and the level is $\gamma\in(0,1)$. Write $q:=(1-d)/(u-d)\in(0,1)$ for the risk-neutral up-probability. Assume moreover (FM)(ii) $p>q$, and let the horizon be $N\ge1$. Put
--
--   $$
--   \gamma_1:=1-\Big(\frac{1-p}{1-q}\Big)^N,\qquad
--   \gamma_2:=p^N\frac{(1-q)^N-(1-p)^N}{\big(p(1-q)\big)^N-\big(q(1-p)\big)^N},
--   $$
--
--   $$
--   \lambda^*=\lambda^*(\gamma):=\min\Big\{\frac{q^N}{p^N-q^N}\,;\ \frac{(1-p)^N(1-\gamma)^{-1}-(1-q)^N}{(1-q)^N-(1-p)^N}\Big\}.
--   $$
--
--   1. The value of (MR) is
--   $$
--   V_{MR}(x_0)=\begin{cases}(\mu-x_0)\lambda^*-x_0 & \text{if }\gamma\ge\gamma_1,\\ -\infty & \text{else.}\end{cases}
--   $$
--   2. The stationary policy $\pi^*=(f^*,\dots,f^*)\in F^N$ is optimal for (MR), where
--   $$
--   f^*(x)=\begin{cases}\dfrac{1}{1-d}\Big((\mu-x_0)\dfrac{q^N}{p^N-q^N}-x_0+x\Big) & \text{if }\gamma\ge\gamma_2,\\[2mm] \dfrac{1}{1-u}\Big((x_0-\mu)\dfrac{(1-q)^N}{(1-q)^N-(1-p)^N}-x_0+x\Big) & \text{if }\gamma_1\le\gamma\le\gamma_2.\end{cases}
--   $$
--
--   The theorem gives the multiperiod mean-risk problem with the Average-Value-at-Risk an explicit value and an explicit optimal portfolio: below the threshold $\gamma_1$ the risk can be made arbitrarily small, and above it the optimal amount invested in the stock is affine in the current wealth.
--
--   Differences from the source:
--   - encoding: the value −∞ of an infimum → ⊥ of an EReal infimum; reason: Lean convention; same instances
--   - encoding: the horizon N of the section (N ≥ 1 implicit, the book's model has at least one period) → hypothesis 1 ≤ N; reason: at N = 0 the constants γ₁, λ* divide by zero and (MR) has no admissible policy; the book's formulas presuppose N ≥ 1, so the hypothesis excludes only undefined cases
--   - encoding: γ₁, γ₂, λ* defined by displays → real variables bound by equation hypotheses; reason: Lean convention; same instances
--   - reading: b) "The optimal policy π* is stationary, i.e. π* = (f*, …, f*) with f*(x) = … if γ ≥ γ₂, … if γ₁ ≤ γ ≤ γ₂" → two clauses: for γ ≥ γ₂ the first policy is optimal, for γ₁ ≤ γ ≤ γ₂ the second; both at γ = γ₂; reason: optimal policies are not unique (at N = 1 both formulas take the same action at x₀ and both are optimal), so the uniqueness reading is false
--   - encoding: the binomial model's 0 < d (§3.1, p.60) → hypothesis 0 < d; reason: the published market structure states only d < 1 < u; the book's assumption is added as a hypothesis
--   - encoding: π = (f₀, …, f_{N−1}) ∈ F^N and the expectation under the path law of the model → π : ℕ → ℝ → ℝ with π n measurable for n < N (values at n ≥ N are ignored) and wealth by pathwise recursion on a probability space with independent R₁, …, R_N of the book law; reason: Lean convention of the published market; every policy gives the same law of X_N
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 4.7.3, p.130 (PDF p.144); constants γ₁, γ₂, λ* p.129 (PDF p.143); Assumption (FM) p.125 (PDF p.139)

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MeanRiskMarket
import Definitions.Def_BauerleRiederMDP_MeanRisk_valueMR
import Definitions.Def_BauerleRiederMDP_MeanRisk_IsOptimalMR

open MeasureTheory

namespace BauerleRiederMDP.MeanRisk

/-- Bäuerle & Rieder (2011), Theorem 4.7.3, p.130 (PDF 144), under Assumption (FM) of §4.7, p.125
(PDF 139), with `γ₁, γ₂, λ*` of p.129 (PDF 143):
`γ₁ := 1 − ((1−p)/(1−q))^N`, `γ₂ := p^N ((1−q)^N − (1−p)^N) / ((p(1−q))^N − (q(1−p))^N)`,
`λ* := min { q^N/(p^N − q^N) ; ((1−p)^N (1−γ)⁻¹ − (1−q)^N)/((1−q)^N − (1−p)^N) }`.

a) `V_MR(x₀) = (μ − x₀)λ* − x₀` if `γ ≥ γ₁`, and `−∞` else.

b) The stationary policy `(f*, …, f*)` is optimal for (MR), with
`f*(x) = (1/(1−d)) ((μ − x₀) q^N/(p^N − q^N) − x₀ + x)` if `γ ≥ γ₂`, and
`f*(x) = (1/(1−u)) ((x₀ − μ) (1−q)^N/((1−q)^N − (1−p)^N) − x₀ + x)` if `γ₁ ≤ γ ≤ γ₂`.

**Formalization Note.** The market is `MDPFinance.MeanVariance.MeanRiskMarket` (binomial model with
`i = 0`, (FM)(i) `d < 1 < u`, (FM)(iii) `0 < x₀ < μ`, `γ ∈ (0,1)`); (FM)(ii) `p > q`, the binomial
model's `d > 0` (§3.1, p.60) and the horizon `N ≥ 1` are hypotheses. `V_MR` is the `EReal` infimum
`valueMR` (`⊥` is `−∞`); `AVaR` is the book's quantile integral. The two formulas of b) are stated as
two clauses; at `γ = γ₂` both apply. -/
theorem theorem_4_7_3 {Ω : Type*} [MeasurableSpace Ω]
    (M : MDPFinance.MeanVariance.MeanRiskMarket Ω)
    (hd : 0 < M.d) (hN : 1 ≤ M.N) (hpq : M.q < M.p) (γ1 γ2 lamstar : ℝ)
    (hγ1 : γ1 = 1 - ((1 - M.p) / (1 - M.q)) ^ M.N)
    (hγ2 : γ2 = M.p ^ M.N * ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N) /
      ((M.p * (1 - M.q)) ^ M.N - (M.q * (1 - M.p)) ^ M.N))
    (hlamstar : lamstar = min (M.q ^ M.N / (M.p ^ M.N - M.q ^ M.N))
      (((1 - M.p) ^ M.N * (1 - M.γ)⁻¹ - (1 - M.q) ^ M.N) /
        ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N))) :
    (γ1 ≤ M.γ → valueMR M = (((M.μ - M.x0) * lamstar - M.x0 : ℝ) : EReal)) ∧
      (M.γ < γ1 → valueMR M = ⊥) ∧
      (γ2 ≤ M.γ → IsOptimalMR M (fun _ x =>
        (1 - M.d)⁻¹ * ((M.μ - M.x0) * (M.q ^ M.N / (M.p ^ M.N - M.q ^ M.N)) - M.x0 + x))) ∧
      (γ1 ≤ M.γ → M.γ ≤ γ2 → IsOptimalMR M (fun _ x =>
        (1 - M.u)⁻¹ * ((M.x0 - M.μ) * ((1 - M.q) ^ M.N / ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N)) -
          M.x0 + x))) := by sorry

end BauerleRiederMDP.MeanRisk
