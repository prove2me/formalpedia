-- Prove2me | Theorems.Thm_BesbesZeevi_SingleParam_lemma2
-- name    : BesbesZeevi.SingleParam.lemma2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:42:23.158494+00:00
-- url     : https://prove2.me/theorems/b9dc091a-a279-40ce-a64a-b4651990dfe9
-- title:
--   Lemma 2: Poisson deviation bounds
-- statement:
--   Let $M,\eta,\beta>0$. There is a constant $C>0$ such that for every $n\ge1$, every $\mu\in[0,M]$ and every $r_n\ge n^\beta$, with
--
--   $$
--   \epsilon_n=2\eta^{1/2}M^{1/2}(\log n)^{1/2}r_n^{-1/2},
--   $$
--
--   a Poisson random variable $N(\mu r_n)$ with mean $\mu r_n$ satisfies
--
--   $$
--   \mathbb P\big(N(\mu r_n)-\mu r_n>r_n\epsilon_n\big)\le\frac{C}{n^\eta},\qquad \mathbb P\big(N(\mu r_n)-\mu r_n<-r_n\epsilon_n\big)\le\frac{C}{n^\eta}.
--   $$
--
--   This is the concentration estimate used to control every demand estimate of the algorithm.
--
--   **Formalization Note** The law of $N(\mu r_n)$ is Mathlib's `poissonMeasure` with mean $\mu r_n$. The constant depends only on $M,\eta,\beta$ and is uniform over $\mu\in[0,M]$ and over $r_n\ge n^\beta$.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 27 (PDF p. 29), Lemma 2

import Mathlib

open MeasureTheory ProbabilityTheory

namespace BesbesZeevi.SingleParam

/-- Lemma 2 (Besbes–Zeevi 2009, p. 27): Poisson deviation bounds. For `μ ∈ [0, M]`,
`r ≥ n^β` and `ε_n = 2 η^{1/2} M^{1/2} (log n)^{1/2} r^{-1/2}`, a Poisson variable `Z` with mean
`μ r` (the law of `N(μ r)`) satisfies `P(Z - μ r > r ε_n) ≤ C/n^η` and
`P(Z - μ r < -r ε_n) ≤ C/n^η` for all `n ≥ 1`, with `C` depending only on `M, η, β`. -/
theorem lemma2 (M η β : ℝ) (hM : 0 < M) (hη : 0 < η) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ μ ∈ Set.Icc (0 : ℝ) M, ∀ r : ℝ, (n : ℝ) ^ β ≤ r →
      (poissonMeasure (μ * r).toNNReal
          {k : ℕ | (k : ℝ) - μ * r >
            r * (2 * Real.sqrt η * Real.sqrt M * Real.sqrt (Real.log n) / Real.sqrt r)}).toReal
          ≤ C / (n : ℝ) ^ η ∧
      (poissonMeasure (μ * r).toNNReal
          {k : ℕ | (k : ℝ) - μ * r <
            -(r * (2 * Real.sqrt η * Real.sqrt M * Real.sqrt (Real.log n) / Real.sqrt r))}).toReal
          ≤ C / (n : ℝ) ^ η := by sorry

end BesbesZeevi.SingleParam
