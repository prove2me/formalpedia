-- Prove2me | Theorems.Thm_AgrawalGoyalTS_NArmed_expected_min_firstExceed_le
-- name    : AgrawalGoyalTS.NArmed.expected_min_firstExceed_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T17:26:20.073979+00:00
-- url     : https://prove2.me/theorems/78d38fab-17fd-42d8-a6b1-ea6de1d07be7
-- title:
--   Lemma 3 — bound on E[E[min{X(j, s(j), y), T} | s(j)]]
-- statement:
--   Let $0<y<\mu_1<1$, $\Delta'=\mu_1-y$,
--   $$R=\frac{\mu_1(1-y)}{y(1-\mu_1)},\qquad D=y\ln\frac{y}{\mu_1}+(1-y)\ln\frac{1-y}{1-\mu_1}$$
--   (the Bernoulli KL divergence between $y$ and $\mu_1$), let $T$ be a positive integer and $j$ a non-negative integer. Let $s(j)\sim\mathrm{Binomial}(j,\mu_1)$ and, given $s(j)=s$, let $X(j,s,y)$ be the number of trials before an independent $\mathrm{Beta}(s+1,j-s+1)$ sequence exceeds $y$. Write
--   $$Q_j=\mathbb E\Big[\mathbb E\big[\min\{X(j,s(j),y),T\}\,\big|\,s(j)\big]\Big]=\sum_{s=0}^{j}\binom js\mu_1^s(1-\mu_1)^{j-s}\,\mathbb E\big[\min\{X(j,s,y),T\}\big].$$
--   Then:
--
--   1. if $j<\frac yD\ln R$, then $Q_j\le 1+\frac{2}{1-y}+\frac{\mu_1}{\Delta'}e^{-Dj}$;
--   2. if $\frac yD\ln R\le j<\frac{4\ln T}{\Delta'^2}$, then $Q_j\le 1+\frac{R^y}{1-y}e^{-Dj}+\frac{\mu_1}{\Delta'}e^{-Dj}$;
--   3. if $j\ge\frac{4\ln T}{\Delta'^2}$, then $Q_j\le\frac{16}{T}$.
--
--   The lemma bounds the expected waiting time between consecutive plays of the optimal arm; in the $N$-armed proof it is applied with $y=\mu_a+\Delta_a/2$ for each suboptimal arm $a$ (Eq. (22)).
--
--   **Formalization Note** The hypotheses $\mu_1<1$ and $T\ge1$ are implicit on the page ($R$ is undefined at $\mu_1=1$). The paper's case display can have overlapping conditions when $\frac{4\ln T}{\Delta'^2}\le j<\frac yD\ln R$, so each bound is stated as an implication under its own condition, which is how the proof in App. C.2 treats it. This is a local copy of the same statement in the two-armed mission of this series.
-- source:
--   Agrawal and Goyal, Analysis of Thompson Sampling for the Multi-armed Bandit Problem, arXiv:1111.1797v3, p. 7, Lemma 3 (proof in App. C.2, pp. 14–16)

import Mathlib
import Definitions.Def_AgrawalGoyalTS_NArmed_BetaBinomial

open MeasureTheory

namespace AgrawalGoyalTS.NArmed

/-- Lemma 3 (p. 7): for `0 < y < μ₁ < 1`, `Δ' = μ₁ - y`, `R = μ₁(1-y)/(y(1-μ₁))`,
`D = y ln(y/μ₁) + (1-y) ln((1-y)/(1-μ₁))`, a positive integer `T` and a natural `j`, the quantity
`E[E[min{X(j, s(j), y), T} | s(j)]]` with `s(j) ∼ Binomial(j, μ₁)` satisfies the three case
bounds, each under its own condition on `j`. -/
theorem expected_min_firstExceed_le (μ₁ y : ℝ) (hy : 0 < y) (hyμ : y < μ₁) (hμ : μ₁ < 1)
    (T : ℕ) (hT : 0 < T) (j : ℕ) :
    let Δ' := μ₁ - y
    let R := μ₁ * (1 - y) / (y * (1 - μ₁))
    let D := y * Real.log (y / μ₁) + (1 - y) * Real.log ((1 - y) / (1 - μ₁))
    let lhs : ENNReal := ∑ s ∈ Finset.range (j + 1), ENNReal.ofReal (AgrawalGoyalTS.TwoArmed.binomPMF j μ₁ s) *
      ∫⁻ ω, min (ENat.toENNReal (AgrawalGoyalTS.TwoArmed.firstExceed y ω)) (T : ENNReal) ∂(AgrawalGoyalTS.TwoArmed.betaTrials s (j - s))
    ((j : ℝ) < y / D * Real.log R →
        lhs ≤ ENNReal.ofReal (1 + 2 / (1 - y) + μ₁ / Δ' * Real.exp (-D * j))) ∧
    (y / D * Real.log R ≤ (j : ℝ) → (j : ℝ) < 4 * Real.log T / Δ' ^ 2 →
        lhs ≤ ENNReal.ofReal
          (1 + R ^ y / (1 - y) * Real.exp (-D * j) + μ₁ / Δ' * Real.exp (-D * j))) ∧
    (4 * Real.log T / Δ' ^ 2 ≤ (j : ℝ) → lhs ≤ ENNReal.ofReal (16 / T)) := by sorry

end AgrawalGoyalTS.NArmed
