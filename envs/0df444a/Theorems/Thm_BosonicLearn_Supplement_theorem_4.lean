-- Prove2me | Theorems.Thm_BosonicLearn_Supplement_theorem_4
-- name    : BosonicLearn.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:01:59.695203+00:00
-- url     : https://prove2.me/theorems/d0553787-5fc2-4a37-97bd-11ec6c65c5f6
-- title:
--   Theorem 4 — adaptive $k$-copy learning of cold Gaussian states needs $\Omega\big(n^3/(\varepsilon^2\min\{\sqrt k,n\})\big)$ copies
-- statement:
--   Work on $n$ bosonic modes, with Gaussian states $\rho(\mu,\Sigma)$ in the convention where the vacuum has covariance $\Sigma=\tfrac12 I_{2n}$. A state is learned to precision $\varepsilon$ when the estimate $\hat\rho$ satisfies $\tfrac12\|\hat\rho-\rho\|_1\le\varepsilon$.
--
--   There are universal constants $\varepsilon_0>0$, $n_0\in\mathbb N$ and $c>0$ such that for every $n\ge n_0$, every $0<\varepsilon<\varepsilon_0$ and every integer $k\ge1$ the following holds. Let $\mathcal A$ be any possibly adaptive protocol that measures at most $k$ fresh copies at a time, keeps no quantum memory between measurements and uses at most $N$ copies in total, followed by any randomized estimator.
--
--   1. If $\mathcal A$ learns every $n$-mode Gaussian state to precision $\varepsilon$ with probability at least $2/3$, then
--   $$N\ \ge\ c\,\frac{n^3}{\varepsilon^2\min\{\sqrt k,\,n\}} .$$
--   2. The same bound holds if $\mathcal A$ is only required to learn the passive Gaussian states whose covariance satisfies
--   $$\Sigma\ \preceq\ \Big(\frac12+\frac1{2n-1}\Big)I_{2n}.$$
--
--   For constant $k$ this is $\Omega(n^3/\varepsilon^2)$, the same as for single-copy measurements, so few-copy entanglement does not lower the cubic scaling. The hard states are cold: their expected total photon number is $O(1)$. The case $k=1$ is the adaptive part of the paper's Theorem 1, and the theorem is the paper's Theorem 2 with the explicit constant $1/(2n-1)$.
--
--   **Formalization Note** $\Omega(\cdot)$ is a constant $c$ chosen with $\varepsilon_0$ and $n_0$, before $n$, $\varepsilon$ and $k$, so it does not depend on $k$. Protocols are `KCopyScheme`s: block sizes in $\{0,\dots,k\}$ chosen measurably from earlier outcomes, with the budget on every transcript; size-$0$ rounds carry stopping and internal randomness. The Loewner bound is positive semidefiniteness of $(\tfrac12+\tfrac1{2n-1})I-\Sigma$. Clause 2 implies clause 1; both are stated.
--
--   Differences from the source:
--   - reading: N = Ω(n³/(ε² min{√k, n})) with "universal constants ε0 > 0 and n0" → ∃ ε₀ > 0, n₀, c > 0 before n, ε, k, the protocol and the estimator, and N ≥ c·n³/(ε² min{√k, n}); reason: the standard reading of Ω with the theorem's own universal constants; c independent of k is what "universal" and the factor min{√k, n} say.
--   - reading: "This remains true under the promise …" → a second clause with the same constants ε₀, n₀, c; reason: "remains true" means the same bound, with the same constants, for the smaller class.
--   - encoding: a possibly adaptive protocol with blocks of at most k fresh copies, at most N copies in total → KCopyScheme with any number R of rounds, block sizes in {0,…,k} measurable in the earlier outcomes, and Σ blocks ≤ N on every transcript; reason: every protocol of the paper (at most N requests of size 1 to k, block sizes depending on earlier outcomes and internal randomness, pp. 26–27) is one, with size-0 rounds drawing the internal randomness before each request; an almost-sure budget becomes an everywhere budget by stopping, with the same transcript laws.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Theorem 4, Eq. (27), p. 23; k-copy model §4, p. 19

import Mathlib
import Definitions.Def_BosonicLearn_Supplement_kCopySuccessProb
import Definitions.Def_BosonicLearn_IsPassive

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicLearn.Supplement

/-- **Theorem 4 (Few-copy lower bound for cold Gaussian states).**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705,
Theorem 4, p. 23: "There exist universal constants ε0 > 0 and n0 ∈ N such that the following holds. Let n ≥ n0,
0 < ε < ε0, and let k ≥ 1 be any integer. Any possibly adaptive protocol that learns every n-mode Gaussian state to
trace-distance error ε with probability at least 2/3, using only k-copy measurements, requires
N = Ω(n³/(ε² min{√k, n})) (27) copies. This remains true under the promise that the unknown state is passive and its
covariance matrix satisfies Σ ≤ (1/2 + 1/(2n−1)) I_{2n}."

There are `ε₀ > 0`, `n₀` and `c > 0` such that for every `n ≥ n₀`, `ε ∈ (0, ε₀)`, every integer `k ≥ 1`, every `N`,
every adaptive `k`-copy protocol with any number `R` of rounds, total budget `N` and any measurable outcome
space, and every (randomized)
estimator:
1. if every `n`-mode Gaussian state is learned to trace distance `ε` with probability at least `2/3`, then
   `N ≥ c · n³/(ε² min{√k, n})`;
2. the same holds if only every passive Gaussian state with `Σ ⪯ (½ + 1/(2n−1)) I` must be learned.

**Formalization Note.** `Ω(·)` is read as a constant `c` chosen together with `ε₀` and `n₀`, before `n`, `ε` and
`k` (so `c` does not depend on `k`). The covariance is the paper's (vacuum `½ I`), see `IsGaussianState`; the
Loewner bound is positive semidefiniteness of `(½ + 1/(2n−1)) I − Σ`. Clause 2 implies clause 1 (its class is
smaller); both are stated. -/
theorem theorem_4 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, n₀ ≤ n →
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ k : ℕ, 1 ≤ k →
      ∀ (R N : ℕ) (O : Type) [MeasurableSpace O] (S : KCopyScheme n k R N O)
        (est : Kernel (Fin R → O) (State (Occupation (Fin n)))), IsMarkovKernel est →
        ((∀ ρ : State (Occupation (Fin n)),
            (∃ (μ : Fin n ⊕ Fin n → ℝ) (Sg : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
              IsGaussianState ρ μ Sg) →
            ENNReal.ofReal (2 / 3) ≤ kCopySuccessProb S est ρ.coefficients ε) →
          c * ((n : ℝ) ^ 3 / (ε ^ 2 * min (Real.sqrt k) (n : ℝ))) ≤ N) ∧
        ((∀ ρ : State (Occupation (Fin n)), IsPassive ρ →
            (∃ (μ : Fin n ⊕ Fin n → ℝ) (Sg : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
              IsGaussianState ρ μ Sg ∧
              ((1 / 2 + 1 / (2 * (n : ℝ) - 1)) •
                (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) - Sg).PosSemidef) →
            ENNReal.ofReal (2 / 3) ≤ kCopySuccessProb S est ρ.coefficients ε) →
          c * ((n : ℝ) ^ 3 / (ε ^ 2 * min (Real.sqrt k) (n : ℝ))) ≤ N) := by sorry

end BosonicLearn.Supplement
