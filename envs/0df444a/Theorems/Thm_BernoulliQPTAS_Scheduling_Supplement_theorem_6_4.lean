-- Prove2me | Theorems.Thm_BernoulliQPTAS_Scheduling_Supplement_theorem_6_4
-- name    : BernoulliQPTAS.Scheduling.Supplement.theorem_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:39:23.387894+00:00
-- url     : https://prove2.me/theorems/5b27c107-f246-48ac-9037-5a75a7d42f0e
-- title:
--   Theorem 6.4 — importance-sampling evaluation of a non-idling policy within $1\pm\rho$
-- statement:
--   Consider Bernoulli jobs on $m\ge1$ machines with $N\ge1$ jobs, $\mu_i=q_ip_i$ and $P=\sum_i\mu_i$. Let $\Pi$ be a non-idling policy, possibly randomized (a law on admissible, non-idling deterministic policies), and let $\rho,\delta\in(0,1)$. Let
--
--   $$
--   n=\bigl\lceil 3N\rho^{-2}\ln(2/\delta)\bigr\rceil .
--   $$
--
--   Run $n$ independent simulations. In each, the policy uses fresh coins, and the realization $\omega$ is drawn from the reweighted distribution $Q$: choose a job $i$ with probability $\mu_i/P$, set $X_i=p_i$, and draw the other outcomes from their own distributions. Record $Z=P\,C(\omega)/V(\omega)$, where $C(\omega)$ is the realized sum of completion times and $V(\omega)=\sum_jX_j(\omega)$. Let $\hat C$ be the average of the $n$ values $Z$. Then
--
--   $$
--   \Pr\bigl[(1-\rho)\,\mathrm{cost}(\Pi)\le\hat C\le(1+\rho)\,\mathrm{cost}(\Pi)\bigr]\ge1-\delta .
--   $$
--
--   This is the evaluation part of Theorem 1.4: exact evaluation is #P-hard (Theorem 6.2), but an estimate within a factor $1\pm\rho$ needs only $O(N\rho^{-2}\log(2/\delta))$ simulations.
--
--   **Formalization Note** The probability is that of the product law of the $n$ independent (coin, realization) pairs. Values of $Z$ and $\hat C$ are extended nonnegative reals with $0/0=0$; under $Q$, $V>0$ almost surely.
--
--   Differences from the source:
--   - generalization: "Let Π be a non-idling policy whose decisions can be simulated in polynomial time" → every non-idling policy, possibly randomized; no simulation-time hypothesis; reason: the hypothesis bounds only the work per simulation, and the probability bound does not use it; the source’s policies are included
--   - encoding: "an estimate Ĉ … can be computed from ⌈3Nρ^{-2} ln(2/δ)⌉ simulations … on realizations drawn from a reweighted distribution" → the estimator of the proof: the average of P·C/V over exactly n i.i.d. simulations, realizations drawn from Q and fresh policy coins in each; reason: fixes the estimator the proof constructs; an unconstrained "estimate" would be trivial
--   - encoding: implicit: N ≥ 1 and m ≥ 1 → hypotheses 0 < N, 0 < m; reason: Q is undefined for P = 0; Section 1.1 assumes 0 < m < N
-- source:
--   Junho Hwang, A QPTAS for Stochastic Scheduling of Bernoulli Jobs, STOC 2027 submission #427 (October 2026), PDF SHA-256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9, Theorem 6.4, p. 19 (proof p. 20); Theorem 1.4, p. 4

import Definitions.Def_BernoulliQPTAS_Scheduling_Supplement_Sampling

open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace BernoulliQPTAS.Scheduling.Supplement

open BernoulliQPTAS.Scheduling MeasureTheory

theorem theorem_6_4 {N m : ℕ} (I : Instance N m) (hm : 0 < m) (hN : 0 < N)
    (π : RandomPolicy N m) (hadm : RandomAdmissible I (initialState Finset.univ) π)
    (hnon : ∀ᵐ t ∂π.law, NonIdling I (initialState Finset.univ) t)
    (ρ δ : ℝ) (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    let n := sampleCount N ρ δ
    ENNReal.ofReal (1 - δ) ≤ samplingLaw I π n
      {xs | ENNReal.ofReal (1 - ρ) * randomCost I π ≤ estimate I n xs ∧
        estimate I n xs ≤ ENNReal.ofReal (1 + ρ) * randomCost I π} := by sorry

end BernoulliQPTAS.Scheduling.Supplement
