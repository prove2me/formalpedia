-- Prove2me | Theorems.Thm_AgrawalGoyalTS_TwoArmed_expected_min_firstExceed_le
-- name    : AgrawalGoyalTS.TwoArmed.expected_min_firstExceed_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:07:26.04315+00:00
-- url     : https://prove2.me/theorems/40a2ed7a-794b-4c39-8a89-a518c25668d2
-- title:
--   Lemma 3 — bound on E[E[min{X(j, s(j), y), T} | s(j)]]
-- statement:
--   Let $0<y<\mu_1<1$, $\Delta'=\mu_1-y$, $R=\frac{\mu_1(1-y)}{y(1-\mu_1)}$ $(>1)$, and let $D=y\ln\frac{y}{\mu_1}+(1-y)\ln\frac{1-y}{1-\mu_1}$ be the KL divergence between Bernoulli($y$) and Bernoulli($\mu_1$). Let $T$ be a positive integer and $j$ a natural number, let $s(j)\sim\mathrm{Binomial}(j,\mu_1)$, and let $X(j,s,y)$ be the number of trials before an i.i.d. $\mathrm{Beta}(s+1,j-s+1)$ sequence first exceeds $y$. Then $\mathbb E\big[\mathbb E[\min\{X(j,s(j),y),T\}\mid s(j)]\big]$ is at most
--   $$\begin{cases}1+\dfrac{2}{1-y}+\dfrac{\mu_1}{\Delta'}e^{-Dj}, & j<\dfrac yD\ln R,\\[2mm] 1+\dfrac{R^y}{1-y}e^{-Dj}+\dfrac{\mu_1}{\Delta'}e^{-Dj}, & \dfrac yD\ln R\le j<\dfrac{4\ln T}{\Delta'^2},\\[2mm] \dfrac{16}{T}, & j\ge\dfrac{4\ln T}{\Delta'^2}.\end{cases}$$
--
--   Applied with $y=\mu_2+\Delta/2$, this bounds the expected waiting time of the optimal arm between consecutive plays and drives the $1/\Delta^3$ term of Theorem 1.
--
--   **Formalization Note** The outer expectation is the finite sum $\sum_{s=0}^j f^B_{j,\mu_1}(s)\,\mathbb E[\min\{X(j,s,y),T\}]$, computed in $[0,\infty]$. The paper states the bound as a case display whose conditions can overlap; it is formalized as three implications, each bound under its own condition. The hypothesis $\mu_1<1$ is implicit in the paper ($R$ and $D$ are undefined at $\mu_1=1$, and $R>1$ is asserted).
-- source:
--   Agrawal and Goyal, Analysis of Thompson Sampling for the Multi-armed Bandit Problem, arXiv:1111.1797v3, p. 7, Lemma 3 (proof in App. C.2, pp. 14–16)

import Mathlib
import Definitions.Def_AgrawalGoyalTS_TwoArmed_BetaBinomial

open MeasureTheory

namespace AgrawalGoyalTS.TwoArmed

/-- Lemma 3 (p. 7): for `0 < y < μ₁ < 1`, `Δ' = μ₁ - y`, `R = μ₁(1-y)/(y(1-μ₁))`,
`D = y ln(y/μ₁) + (1-y) ln((1-y)/(1-μ₁))`, a positive integer `T` and a natural `j`, the quantity
`E[E[min{X(j, s(j), y), T} | s(j)]]` with `s(j) ∼ Binomial(j, μ₁)` satisfies the three case
bounds, each under its own condition on `j`. -/
theorem expected_min_firstExceed_le (μ₁ y : ℝ) (hy : 0 < y) (hyμ : y < μ₁) (hμ : μ₁ < 1)
    (T : ℕ) (hT : 0 < T) (j : ℕ) :
    let Δ' := μ₁ - y
    let R := μ₁ * (1 - y) / (y * (1 - μ₁))
    let D := y * Real.log (y / μ₁) + (1 - y) * Real.log ((1 - y) / (1 - μ₁))
    let lhs : ENNReal := ∑ s ∈ Finset.range (j + 1), ENNReal.ofReal (binomPMF j μ₁ s) *
      ∫⁻ ω, min (ENat.toENNReal (firstExceed y ω)) (T : ENNReal) ∂(betaTrials s (j - s))
    ((j : ℝ) < y / D * Real.log R →
        lhs ≤ ENNReal.ofReal (1 + 2 / (1 - y) + μ₁ / Δ' * Real.exp (-D * j))) ∧
    (y / D * Real.log R ≤ (j : ℝ) → (j : ℝ) < 4 * Real.log T / Δ' ^ 2 →
        lhs ≤ ENNReal.ofReal
          (1 + R ^ y / (1 - y) * Real.exp (-D * j) + μ₁ / Δ' * Real.exp (-D * j))) ∧
    (4 * Real.log T / Δ' ^ 2 ≤ (j : ℝ) → lhs ≤ ENNReal.ofReal (16 / T)) := by sorry

end AgrawalGoyalTS.TwoArmed
