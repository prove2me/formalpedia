-- Prove2me | Theorems.Thm_DPVerify_lemma_4_2
-- name    : DPVerify.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:54:22.938306+00:00
-- url     : https://prove2.me/theorems/c3900e35-6e8c-4361-91f8-5fbdb5cdc3e7
-- title:
--   Lemma 4.2 — $(\varepsilon,\delta)$-DP with $\varepsilon=\rho/\sqrt{8m\log(1/\rho)}$ bounds the max-information: $I^{\rho^3}_\infty(S;\mathcal A(S))\le O(\rho)$
-- statement:
--   This is Corollary 3.12 of Rogers, Roth, Smith and Thakkar [RRST16], as restated in the paper.
--
--   There are constants $\rho_0\in(0,1)$ and $K>0$ such that the following holds. Let $m\ge1$, let $\rho\in(0,\rho_0)$, and set
--
--   $$
--   \varepsilon=\frac{\rho}{\sqrt{8m\log(1/\rho)}},\qquad 0\le\delta\le\frac{\varepsilon\rho^6}{m^2}.
--   $$
--
--   Let $\mathcal A:\mathcal X^m\to\mathcal Y$ be an $(\varepsilon,\delta)$-differentially private algorithm. Then for every distribution $D$ on $\mathcal X$, if $S\sim D^m$,
--
--   $$
--   I^{\rho^3}_\infty(S;\mathcal A(S))\;\le\;K\rho .
--   $$
--
--   This is the first step of the transfer from differential privacy to replicability used in Corollary 4.5: with $\varepsilon$ of order $1/\sqrt m$, the output of a private algorithm carries little information about its sample.
--
--   Differences from the source:
--   - reading: fix $m$, sufficiently small $\rho\in(0,1)$; $I^{\rho^3}_\infty\le O(\rho)$ → there are $\rho_0\in(0,1)$ and $K>0$, chosen before $\mathcal X$, $\mathcal Y$, $m$ and $\mathcal A$, with the bound $K\rho$ for all $\rho\in(0,\rho_0)$; reason: the only reading with content; Corollary 4.5 applies the lemma with $m=s$ for every $s$, so the threshold and the constant must not depend on $m$
--   - encoding: $m\in\mathbb N$ → $m\ge1$; reason: at $m=0$ the formula for $\varepsilon$ divides by zero
--   - reading: $\log$ in Definition 2.3 → natural logarithm: $I^\beta_\infty\le k$ as $\Pr[(S,\mathcal A(S))\in O]\le e^k\Pr[S\otimes\mathcal A(S)\in O]+\beta$ for every measurable $O$; reason: Definition 2.3 does not fix the base; Definitions 2.2 and 2.4 use $e^\varepsilon$; the linear form is equivalent to the sup-log form
--   - reading: adjacent datasets differ by the addition or removal of one element (Definition 2.1) → neighbouring samples in $\mathcal X^s$ differ in one coordinate; reason: every protocol of the paper reads a sample of fixed size, and §6 (p.33) proves privacy for neighbouring datasets which differ on the $i$th coordinate
--   - encoding: an algorithm $\mathcal A:\mathcal X^m\to\mathcal Y$, any distribution $D$ → a randomized algorithm with explicit coins, jointly measurable, between arbitrary measurable spaces; $D$ a probability measure; reason: Lean representation; makes every probability defined
--   - reading: $\delta\le\varepsilon\rho^6/m^2$ → $0\le\delta\le\varepsilon\rho^6/m^2$; reason: privacy parameters are nonnegative throughout the paper
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Lemma 4.2, p.18 (PDF p.21)

import Mathlib
import Definitions.Def_DPVerify_RandAlg
import Definitions.Def_DPVerify_IsDPAlg
import Definitions.Def_DPVerify_MaxInfoLE

set_option autoImplicit false

open MeasureTheory

namespace DPVerify

/-- Lemma 4.2 (Corollary 3.12 of [RRST16]; Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), p.18 = PDF p.21): differential privacy bounds the
max-information. There are `ρ₀ ∈ (0, 1)` and `K > 0` such that for every `m ≥ 1` and
`ρ ∈ (0, ρ₀)`, with `ε = ρ / √(8 m log(1/ρ))` and `0 ≤ δ ≤ ε ρ⁶ / m²`, every `(ε, δ)`-DP algorithm
`A : X^m → Y` and every distribution `D` satisfy `I^{ρ³}_∞(S; A(S)) ≤ K ρ` for `S ∼ D^m`.

**Formalization Note** "Sufficiently small `ρ`" and "`≤ O(ρ)`" are read with `ρ₀` and `K`
quantified before `X`, `Y`, `m` and `A` (uniform in all of them), which is what Corollary 4.5
needs. The logarithm is natural. `m ≥ 1` excludes the case where `ε` divides by zero. -/
theorem lemma_4_2 :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ < 1 ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (m : ℕ), 0 < m →
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
      ∀ δ : ℝ, 0 ≤ δ →
        δ ≤ ρ / Real.sqrt (8 * m * Real.log (1 / ρ)) * ρ ^ 6 / (m : ℝ) ^ 2 →
      ∀ A : RandAlg X Y m, IsDPAlg A (ρ / Real.sqrt (8 * m * Real.log (1 / ρ))) δ →
      ∀ D : ProbabilityMeasure X, MaxInfoLE A D (ρ ^ 3) (K * ρ) := by sorry

end DPVerify
