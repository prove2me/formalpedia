-- Prove2me | Theorems.Thm_BesbesZeevi_Nonparametric_lemma2_poisson_deviation
-- name    : BesbesZeevi.Nonparametric.lemma2_poisson_deviation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:07:00.636682+00:00
-- url     : https://prove2.me/theorems/3f7e9d5b-8f87-40f6-b1e7-35a22425a914
-- title:
--   Lemma 2: Poisson deviation bound $\mathbb P(|N(\mu r_n)-\mu r_n|>r_n\epsilon_n)\le C/n^\eta$
-- statement:
--   Let $M,\eta,\beta>0$. There is a constant $C>0$, depending only on $M,\eta,\beta$, with the following property.
--
--   Let $(r_n)$ be any sequence with $r_n\ge n^\beta$ for all $n\ge1$, and let $\mu\in[0,M]$. Put
--
--   $$
--   \epsilon_n=2\eta^{1/2}M^{1/2}(\log n)^{1/2}r_n^{-1/2},
--   $$
--
--   and let $N(\mu r_n)$ be a Poisson random variable with mean $\mu r_n$. Then for all $n\ge1$,
--
--   $$
--   \mathbb P\big(N(\mu r_n)-\mu r_n>r_n\epsilon_n\big)\le\frac{C}{n^\eta},\qquad
--   \mathbb P\big(N(\mu r_n)-\mu r_n<-r_n\epsilon_n\big)\le\frac{C}{n^\eta}.
--   $$
--
--   This bound controls the demand estimates of the learning phase.
--
--   **Formalization Note** $N(\mu r_n)$ is represented by its law, Mathlib's `poissonMeasure` with mean $\mu r_n$. The constant is quantified before the sequence $(r_n)$ and before $\mu$: it is uniform in them, as the paper's proof shows and as the later lemmas use it.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 27 (PDF 29), Lemma 2

import Mathlib

open MeasureTheory ProbabilityTheory

namespace BesbesZeevi.Nonparametric

/-- Lemma 2, p. 27: for `μ ∈ [0, M]`, `r_n ≥ n^β` (`β > 0`) and
`ε_n = 2 η^{1/2} M^{1/2} (log n)^{1/2} r_n^{-1/2}`, a Poisson variable `N(μ r_n)` with mean `μ r_n`
satisfies `P(N(μ r_n) - μ r_n > r_n ε_n) ≤ C/n^η` and `P(N(μ r_n) - μ r_n < -r_n ε_n) ≤ C/n^η`
for all `n ≥ 1`, with `C` depending only on `M, η, β`. -/
theorem lemma2_poisson_deviation (M η β : ℝ) (hM : 0 < M) (hη : 0 < η) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧
      ∀ r : ℕ → ℝ, (∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ β ≤ r n) →
        ∀ μ ∈ Set.Icc (0 : ℝ) M, ∀ n : ℕ, 1 ≤ n →
          poissonMeasure (Real.toNNReal (μ * r n))
              {k : ℕ | (k : ℝ) - μ * r n >
                r n * (2 * Real.sqrt η * Real.sqrt M * Real.sqrt (Real.log n) / Real.sqrt (r n))}
            ≤ ENNReal.ofReal (C / (n : ℝ) ^ η) ∧
          poissonMeasure (Real.toNNReal (μ * r n))
              {k : ℕ | (k : ℝ) - μ * r n <
                -(r n * (2 * Real.sqrt η * Real.sqrt M * Real.sqrt (Real.log n) / Real.sqrt (r n)))}
            ≤ ENNReal.ofReal (C / (n : ℝ) ^ η) := by sorry

end BesbesZeevi.Nonparametric
