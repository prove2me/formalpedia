-- Prove2me | Theorems.Thm_BauerleRiederMDP_MeanRisk_proposition_4_7_2
-- name    : BauerleRiederMDP.MeanRisk.proposition_4_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:30:15.019209+00:00
-- url     : https://prove2.me/theorems/3b7e6765-96cf-40cd-becd-e593fa09940a
-- title:
--   Proposition 4.7.2 — value and optimal stationary policies of the Lagrange problem $P(\lambda)$
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
--   For $\lambda\ge0$:
--
--   1. The value of $P(\lambda)$ is
--   $$
--   \inf_{\pi\in F^N}L_{x_0}(\pi,\lambda)=\begin{cases}(\mu-x_0)\lambda-x_0 & \text{if }\lambda\in[0,\lambda^*],\ \gamma\ge\gamma_1,\\ -\infty & \text{else.}\end{cases}
--   $$
--   2. With $f^b(x):=\max\big\{\frac{x+b}{1-u},\frac{x+b}{1-d}\big\}$ (the optimal decision rule of $P(\lambda,b)$, Theorem 4.7.1), the stationary policy $(f^b,\dots,f^b)$ is optimal for $P(\lambda)$ exactly for $b=-x_0$ if $\lambda\in[0,\lambda^*)$; for every $b\in[-x_0,\infty)$ if $\lambda=\lambda^*$ and $\gamma\ge\gamma_2$; and for every $b\in(-\infty,-x_0]$ if $\lambda=\lambda^*$ and $\gamma_1\le\gamma\le\gamma_2$.
--
--   This is the dual step of the Lagrange approach: maximizing the value in 1 over $\lambda\ge0$ gives the value of (MR) in Theorem 4.7.3, and the policies in 2 are the candidates for the optimal policy of (MR).
--
--   Differences from the source:
--   - encoding: the value −∞ of an infimum → ⊥ of an EReal infimum; reason: Lean convention; same instances
--   - encoding: the horizon N of the section (N ≥ 1 implicit, the book's model has at least one period) → hypothesis 1 ≤ N; reason: at N = 0 the constants γ₁, λ* divide by zero and (MR) has no admissible policy; the book's formulas presuppose N ≥ 1, so the hypothesis excludes only undefined cases
--   - encoding: γ₁, γ₂, λ* defined by displays → real variables bound by equation hypotheses; reason: Lean convention; same instances
--   - reading: b) "The optimal policy π* for P(λ) is stationary, i.e. π* = (f^b, . . . , f^b) with b ∈ {−x₀} / [−x₀, ∞) / (−∞, −x₀]" → (f^b, …, f^b) is optimal for P(λ) iff b = −x₀ when λ ∈ [0, λ*), and for each b in the listed set when λ = λ*; reason: the set {−x₀} is exact for λ < λ* (the proof on p.130 says the minimum point is unique), but at λ = λ* the converse is false: e.g. N = 1, u = 2, d = 1/2, p = 1/2, γ = 3/4, λ = λ* = 2 and b = −2 < −x₀ = −1 gives an optimal policy, since at N = 1 only the first action matters
--   - encoding: the binomial model's 0 < d (§3.1, p.60) → hypothesis 0 < d; reason: the published market structure states only d < 1 < u; the book's assumption is added as a hypothesis
--   - encoding: π = (f₀, …, f_{N−1}) ∈ F^N and the expectation under the path law of the model → π : ℕ → ℝ → ℝ with π n measurable for n < N (values at n ≥ N are ignored) and wealth by pathwise recursion on a probability space with independent R₁, …, R_N of the book law; reason: Lean convention of the published market; every policy gives the same law of X_N
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Proposition 4.7.2, p.129 (PDF p.143); constants γ₁, γ₂, λ* p.129; Assumption (FM) p.125 (PDF p.139)

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MeanRiskMarket
import Definitions.Def_BauerleRiederMDP_MeanRisk_valuePLambda
import Definitions.Def_BauerleRiederMDP_MeanRisk_IsOptimalPLambda

open MeasureTheory

namespace BauerleRiederMDP.MeanRisk

/-- Bäuerle & Rieder (2011), Proposition 4.7.2, p.129 (PDF 143), under Assumption (FM) of §4.7,
p.125 (PDF 139). Put `γ₁ := 1 − ((1−p)/(1−q))^N`,
`γ₂ := p^N ((1−q)^N − (1−p)^N) / ((p(1−q))^N − (q(1−p))^N)` and
`λ* := min { q^N/(p^N − q^N) ; ((1−p)^N (1−γ)⁻¹ − (1−q)^N)/((1−q)^N − (1−p)^N) }`. For `λ ≥ 0`:

a) `inf_{π ∈ F^N} L_{x₀}(π, λ) = (μ − x₀)λ − x₀` if `λ ∈ [0, λ*]` and `γ ≥ γ₁`, and `−∞` else;

b) the stationary policy `(f^b, …, f^b)`, `f^b(x) = max {(x+b)/(1−u), (x+b)/(1−d)}` (Theorem 4.7.1),
is optimal for `P(λ)` exactly for `b = −x₀` if `λ ∈ [0, λ*)`, for every `b ∈ [−x₀, ∞)` if `λ = λ*`,
`γ ≥ γ₂`, and for every `b ∈ (−∞, −x₀]` if `λ = λ*`, `γ₁ ≤ γ ≤ γ₂`.

**Formalization Note.** The market is `MDPFinance.MeanVariance.MeanRiskMarket` (binomial model with
`i = 0`, (FM)(i) `d < 1 < u`, (FM)(iii) `0 < x₀ < μ`, `γ ∈ (0,1)`); (FM)(ii) `p > q`, the binomial
model's `d > 0` (§3.1, p.60) and the horizon `N ≥ 1` are hypotheses. `γ₁, γ₂, λ*` are bound by
equations. Part b) is read as: for `λ ∈ [0, λ*)` the singleton `{−x₀}` is exactly the set of `b` with `(f^b, …, f^b)`
optimal; for `λ = λ*` each policy listed is optimal (the converse fails there at `N = 1`). -/
theorem proposition_4_7_2 {Ω : Type*} [MeasurableSpace Ω]
    (M : MDPFinance.MeanVariance.MeanRiskMarket Ω)
    (hd : 0 < M.d) (hN : 1 ≤ M.N) (hpq : M.q < M.p) (γ1 γ2 lamstar : ℝ)
    (hγ1 : γ1 = 1 - ((1 - M.p) / (1 - M.q)) ^ M.N)
    (hγ2 : γ2 = M.p ^ M.N * ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N) /
      ((M.p * (1 - M.q)) ^ M.N - (M.q * (1 - M.p)) ^ M.N))
    (hlamstar : lamstar = min (M.q ^ M.N / (M.p ^ M.N - M.q ^ M.N))
      (((1 - M.p) ^ M.N * (1 - M.γ)⁻¹ - (1 - M.q) ^ M.N) /
        ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N)))
    (lam : ℝ) (hlam : 0 ≤ lam) :
    (lam ≤ lamstar ∧ γ1 ≤ M.γ →
        valuePLambda M lam = (((M.μ - M.x0) * lam - M.x0 : ℝ) : EReal)) ∧
      (¬ (lam ≤ lamstar ∧ γ1 ≤ M.γ) → valuePLambda M lam = ⊥) ∧
      (lam < lamstar → ∀ b : ℝ, IsOptimalPLambda M lam
        (fun _ x => max ((x + b) / (1 - M.u)) ((x + b) / (1 - M.d))) ↔ b = -M.x0) ∧
      (lam = lamstar → γ2 ≤ M.γ → ∀ b : ℝ, -M.x0 ≤ b → IsOptimalPLambda M lam
        (fun _ x => max ((x + b) / (1 - M.u)) ((x + b) / (1 - M.d)))) ∧
      (lam = lamstar → γ1 ≤ M.γ → M.γ ≤ γ2 → ∀ b : ℝ, b ≤ -M.x0 → IsOptimalPLambda M lam
        (fun _ x => max ((x + b) / (1 - M.u)) ((x + b) / (1 - M.d)))) := by sorry

end BauerleRiederMDP.MeanRisk
