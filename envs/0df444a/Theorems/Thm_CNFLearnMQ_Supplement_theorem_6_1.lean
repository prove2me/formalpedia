-- Prove2me | Theorems.Thm_CNFLearnMQ_Supplement_theorem_6_1
-- name    : CNFLearnMQ.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:05:06.526095+00:00
-- url     : https://prove2.me/theorems/040ff725-8cc3-4869-95b9-fa0dbd6d1aa8
-- title:
--   Theorem 6.1 — CoreSieve exactly learns random $k$-CNFs in time $O_{k,\alpha}(n^{2+\eta_k}(\ln n)^k(\ln(n/\delta))^2)$
-- statement:
--   Let $k\ge10^5$ and $\alpha>0$ be constants with $\alpha\le 2^{k-30k^{4/5}\log k}/(2^{10}e^2k^8)$, and let $\eta_k=4096k^{6/5}\cdot2^{-k^{4/5}}$. There are constants $C>0$, an integer $a$, a threshold $n_0$ and a function $g$ with $n\,g(n)\to0$, all depending only on $k$ and $\alpha$, such that the following holds for every $n\ge n_0$ and every confidence parameter $\delta\in(0,1)$. With probability at least $1-g(n)$ over the random formula $\Phi=\Phi(k,n,\lfloor\alpha n\rfloor)$, $\Phi$ is satisfiable and CoreSieve$(\delta)$, run with sample access to $\mu_\Phi$ and membership-query access to $\Phi$,
--
--   1. outputs a formula $\widehat\Phi$ with $\mu_{\widehat\Phi}=\mu_\Phi$ with probability at least $1-\delta$;
--   2. always runs in time at most
--   $$C\,n^{2+\eta_k}(\ln n)^k\Bigl(\ln\frac n\delta\Bigr)^2;$$
--   3. always draws at most $C\,n^{\eta_k}(\ln(n/\delta))^a$ samples;
--   4. always asks at most $C\,n^{1+\eta_k}(\ln(n/\delta))^a$ membership queries.
--
--   In particular CoreSieve solves the exact learning problem of Definition 1.3 with confidence $\delta$. With membership queries the running-time exponent is $2+\eta_k$, arbitrarily close to $2$ for large $k$, in the density regime $\alpha\le 2^{k-\widetilde O(k^{4/5})}$; sample-only learning by Valiant's algorithm needs time $n^{O(k)}$.
--
--   Differences from the source:
--   - encoding: there is an algorithm → the paper's Algorithm 5 (`coreSieve`) with the published LearnCore, explicit time charges and a fixed enumeration order; reason: the theorem is proved by analysing Algorithm 5; the output set does not depend on the order
--   - encoding: time $O_{k,\alpha}(\cdot)$, sample and query complexity $\widetilde O_{k,\alpha}(\cdot)$ hiding polylogarithms in $n,1/\delta$ → constants $C>0$ and $a$ chosen from $k,\alpha$; every outcome of positive probability obeys the bounds; the polylogarithmic factor is $(\ln(n/\delta))^a$; reason: worst-case reading of the paper's bounds; for $\delta<1$, $\ln(n/\delta)\ge\max(\ln n,\ln(1/\delta))$
--   - generalization: outer probability $1-o(1/n)$ in Definition 1.3, for the fixed $\delta$ → one function $g$ with $n\,g(n)\to0$, chosen before $\delta$, serving every $\delta\in(0,1)$; reason: specializes to the per-$\delta$ statement; the proof's failure event (Lemma 6.2) does not involve $\delta$
--   - reading: the algorithm uses the stated time, samples and queries on the random formula → the resource bounds are part of the event of probability at least $1-g(n)$ over $\Phi$; reason: the proof bounds the resources for a fixed $\Phi$ with the properties of Lemma 6.2 (p.38); the paper states nothing about the remaining formulas
--   - encoding: $\mu_{\widehat\Phi}=\mu_\Phi$; random formula $\Phi=(V,\mathcal C)$ → equal solution sets for a satisfiable $\Phi$ (an unsatisfiable $\Phi$ counts as a failure); $\Phi$ a finite set of clauses, identical clauses kept once; reason: both laws are uniform on their solution sets; merging identical clauses leaves the solution set unchanged
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Theorem 6.1, p.37; Definition 1.3, p.4; Algorithm 5, p.39

import Mathlib
import Definitions.Def_CNFLearnMQ_Supplement_coreSieve
import Definitions.Def_CNFLearnMQ_memOracle

set_option autoImplicit false

namespace CNFLearnMQ.Supplement

open CNFLearning873.Valiant CNFLearnMQ Filter Topology

/-- Theorem 6.1, p.37 (Feng, Yu, Zhang, *Learning CNF Formulas with Uniform Random Solutions and
Membership Queries*, STOC 2027 submission (manuscript sha256 519ee6d4…)), with the exact learning
problem of Definition 1.3, p.4. Let `k ≥ 10⁵` and `α > 0` with
`α ≤ 2^{k − 30k^{4/5} log k}/(2^{10}e²k⁸)`, and `η_k = 4096k^{6/5}·2^{−k^{4/5}}`. There are constants
`C > 0`, `a`, `n₀` and a function `g` with `n·g(n) → 0` (i.e. `g(n) = o(1/n)`), all depending only on
`k, α`, such that for every `n ≥ n₀` and every confidence parameter `δ ∈ (0, 1)`, with probability at
least `1 − g(n)` over the random formula `Φ = Φ(k, n, ⌊αn⌋)`: `Φ` is satisfiable, and CoreSieve(δ)
(Algorithm 5), run with sample access to `µ_Φ` and membership-query access to `Φ`,
1. outputs `Φ̂` with `µ_Φ̂ = µ_Φ` (equal solution sets) with probability at least `1 − δ`;
2. always runs in time at most `C·n^{2+η_k}·(ln n)^k·(ln(n/δ))²`;
3. always draws at most `C·n^{η_k}·(ln(n/δ))^a` samples;
4. always asks at most `C·n^{1+η_k}·(ln(n/δ))^a` membership queries.

**Formalization Note** "There is an algorithm" is witnessed by the paper's own Algorithm 5,
`coreSieve`, which receives only `n, k, α, δ`. Time is the unit-cost charge of `run` and of the
definitions; "always" means every outcome of positive probability. `O_{k,α}` and `Õ_{k,α}` (which
hides polylogarithms in `n` and `1/δ`; for `δ < 1`, `ln(n/δ) ≥ max(ln n, ln(1/δ))`) are read with
`C, a` chosen from `k, α`. The outer `1 − o(1/n)` of Definition 1.3 is `1 − g(n)` with
`n·g(n) → 0`; `g` is chosen before `δ`, which implies the per-`δ` reading. Unsatisfiable `Φ` has
no `µ_Φ` and counts as a failure. The resource bounds are part of the high-probability event over
`Φ`, as in the proof (which fixes `Φ` with the properties of Lemma 6.2). -/
theorem theorem_6_1 (k : ℕ) (α : ℝ) (hk : 10 ^ 5 ≤ k) (hα : 0 < α)
    (hαk : α ≤ densityBound k) :
    ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∃ n₀ : ℕ, ∃ g : ℕ → ℝ,
      Tendsto (fun n : ℕ => (n : ℝ) * g n) atTop (𝓝 0) ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ δ : ℝ, 0 < δ → δ < 1 →
        ENNReal.ofReal (1 - g n) ≤ prob (randomCNF k n ⌊α * n⌋₊) (fun Φ =>
          ∃ h : (solutions Φ).Nonempty,
            ENNReal.ofReal (1 - δ) ≤
              prob (run (solutionPMF Φ h) (memOracle Φ) (coreSieve n k α δ))
                (fun o => solutions o.1 = solutions Φ) ∧
            (∀ o ∈ (run (solutionPMF Φ h) (memOracle Φ) (coreSieve n k α δ)).support,
              (o.2.time : ℝ) ≤ C * (n : ℝ) ^ (2 + etaK k) * Real.log n ^ k *
                Real.log ((n : ℝ) / δ) ^ 2) ∧
            (∀ o ∈ (run (solutionPMF Φ h) (memOracle Φ) (coreSieve n k α δ)).support,
              (o.2.samples : ℝ) ≤ C * (n : ℝ) ^ etaK k * Real.log ((n : ℝ) / δ) ^ a) ∧
            (∀ o ∈ (run (solutionPMF Φ h) (memOracle Φ) (coreSieve n k α δ)).support,
              (o.2.queries : ℝ) ≤ C * (n : ℝ) ^ (1 + etaK k) * Real.log ((n : ℝ) / δ) ^ a)) := by sorry

end CNFLearnMQ.Supplement
