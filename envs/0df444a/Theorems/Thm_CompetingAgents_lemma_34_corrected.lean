-- Prove2me | Theorems.Thm_CompetingAgents_lemma_34_corrected
-- name    : CompetingAgents.lemma_34_corrected
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:26:56.556998+00:00
-- url     : https://prove2.me/theorems/f0812dbe-906b-4329-baab-2fb4eb07b5e0
-- title:
--   Lemma 34 (corrected: the pathwise bound $|\hat S^t_n-s(\beta)|\le\sum_{i=0}^{t-1}\kappa^iD_{t-i}+\kappa^tC$)
-- statement:
--   Let $(\hat S^t_n)_{t\ge0}$ be the process (4.1) from an initial threshold $\hat S^0_n\in\mathbb R$, let $\kappa\ge0$ be a Lipschitz constant of $q(P(\beta,\cdot))$, let $s(\beta)$ be a fixed point of $q(P(\beta,\cdot))$, and let
--
--   $$D_k=\big|q\big(P^n(\beta,\hat S^{k-1}_n)\big)-q\big(P(\beta,\hat S^{k-1}_n)\big)\big|=\big|\hat S^k_n-q\big(P(\beta,\hat S^{k-1}_n)\big)\big|,\qquad k\ge1.$$
--
--   Then on every outcome and for every $t\ge0$,
--
--   $$\big|\hat S^t_n-s(\beta)\big|\le\sum_{i=0}^{t-1}\kappa^i D_{t-i}+\kappa^t\,\big|\hat S^0_n-s(\beta)\big|.$$
--
--   The printed Lemma 34 states that $\sum_{i=1}^t z^{t-i}\kappa^i+\kappa^tC$ stochastically dominates $|\hat S^t_n-s(\beta)|$. That is false (see below). Its proof, (I.18)–(I.24) on p.54, derives the recursion $|\hat S^t_n-s(\beta)|\le D_t+\kappa|\hat S^{t-1}_n-s(\beta)|$; unrolled, it gives this pathwise bound, which carries weight $\kappa^0$ on the newest error. Together with Lemma 33 (corrected) and a union bound it proves Theorem 4.
--
--   Differences from the source:
--
--   - correction: $\sum_{i=1}^{t}z^{t-i}\kappa^i+\kappa^tC$ stochastically dominates $|\hat S^t_n-s(\beta)|$ → $|\hat S^t_n-s(\beta)|\le\sum_{i=0}^{t-1}\kappa^iD_{t-i}+\kappa^tC$ on every outcome; reason: the printed lemma is false: it inherits the failure of Lemma 33, and its sum is mis-indexed. In the instance of Lemma 33 (corrected) with $t=1$ and $\hat S^0_n=s(\beta)$, $C=0$ and the printed bound is $\kappa z^0$ with $\kappa\le0.0025$, while $|\hat S^1_n-s(\beta)|\ge3$ with probability about $6.7\cdot10^{-11}$. The corrected statement is the recursion (I.18)–(I.24) unrolled, with the sum from $i=0$
--   - generalization: the conditions of Theorem 4; $\kappa$ the Lipschitz constant of $q(P(\beta,s))$ → no model hypotheses; any Lipschitz constant $\kappa\ge0$ and any fixed point; reason: the pathwise inequality uses only the Lipschitz property and the fixed-point equation; the source's setting is a special case
--   - generalization: Assumption 2: the $(Z,c)$-marginal of $F$ has finite support; $c_i\in\mathcal C\subset L^2(\tilde{\mathcal X},dx)$ with $\mathcal C$ convex and compact; outcomes $Y_i(0),Y_i(1)$ (pp.6, 8) → finitely many types $i\in\iota$ with weights $w_i>0$, $\sum_i w_i=1$; no membership in $\mathcal C$ is required and the outcomes are not modelled; reason: no statement of the mission mentions $\mathcal C$ or the outcomes, and the score law does not depend on them; every instance of the source is an instance of the Lean model
--   - reading: the $q$-th quantile $q(\cdot)$ → the lower quantile $\inf\{r : q\le G(r)\}$; reason: the convention of Shao (2003), cited for Theorem 17; for $P(\beta,s)$ it is the unique inverse of Lemma 30
--   - reading: the process (4.1); the running text of p.9 prints $\hat S^t_n=q(P^{n,t-1})$ → display (4.1): $\hat S^t_n=q(P^n(\beta,\hat S^{t-1}_n))$, where cohort $t$ is a fresh sample, independent over all $(t,j)$, each agent with law $F$, responding to the realized $\hat S^{t-1}_n$; reason: display (4.1) is the definition and the text says that $n$ new agents are sampled i.i.d. at each step
-- source:
--   Sahoo, Wager, Policy Learning with Competing Agents, arXiv:2204.01884v5, Lemma 34, p.36, and (I.18)–(I.24), p.54

import Mathlib
import Definitions.Def_CompetingAgents_thresholdProcess

open scoped NNReal

namespace CompetingAgents

/-- Lemma 34, corrected (Sahoo, Wager, *Policy Learning with Competing Agents*, arXiv:2204.01884v5,
Lemma 34, p.36, and its proof (I.18)–(I.24), p.54). Let `Ŝⁿₜ` be the process (4.1), let `κ` be a
Lipschitz constant of `q(P(β, ·))` and `s(β)` a fixed point of it, and
`Dₖ = |q(Pⁿ(β, Ŝⁿₖ₋₁)) − q(P(β, Ŝⁿₖ₋₁))| = |Ŝⁿₖ − q(P(β, Ŝⁿₖ₋₁))|`. Then on every outcome
`|Ŝⁿₜ − s(β)| ≤ ∑_{i=0}^{t−1} κⁱ D_{t−i} + κᵗ |Ŝⁿ₀ − s(β)|`.

**Formalization Note.** The printed Lemma 34 (stochastic dominance by `∑_{i=1}^t z^{t−i} κⁱ + κᵗC`)
is false; this is the pathwise inequality its proof derives in (I.18)–(I.24), with the sum indexed
from `i = 0`, which is where the recursion puts weight `κ⁰` on the newest term. It holds for every
realization of the cohorts, so no probabilistic hypothesis is needed; `D_{t−i}` is written with
`t − i = (t − (i + 1)) + 1`, exact for `i < t`. -/
theorem lemma_34_corrected {d : ℕ} {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    (M : Model d ι) (β : Cov d) (n : ℕ) (S0 : ℝ) {Ω : Type*} (A : ℕ → Fin n → Ω → ι × Cov d)
    (κ : ℝ≥0) (hκ : LipschitzWith κ (eqMap M β)) (sβ : ℝ) (hsβ : sβ = eqMap M β sβ)
    (t : ℕ) (ω : Ω) :
    |thresholdProcess M β n S0 A t ω - sβ| ≤
      ∑ i ∈ Finset.range t, (κ : ℝ) ^ i *
        |thresholdProcess M β n S0 A (t - i) ω -
          eqMap M β (thresholdProcess M β n S0 A (t - (i + 1)) ω)| +
      (κ : ℝ) ^ t * |S0 - sβ| := by sorry

end CompetingAgents
