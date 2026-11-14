-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_random_uniform_survival
-- name    : CountingLLL.ReciprocalTest.random_uniform_survival
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:37:58.164815+00:00
-- url     : https://prove2.me/theorems/99a5ab91-5f55-45e8-91a3-89b8b8fadc7c
-- title:
--   Survival of a random number of independent uniform return tests
-- statement:
--   Let $K$ be a finite random nonnegative integer. Independently of $K$, draw for each $i\geq0$ a uniform element from a set of $i+2$ elements with one distinguished value. The probability that each of the first $K$ draws avoids its distinguished value equals $\mathbb E[1/(K+1)]$. This is the probabilistic survival identity used in the suppressed-return analysis of ReciprocalTest. Establishing that its adaptive execution has this product coupling is a separate task.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, proof of Lemma 6.5, correctness, p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalTest
open CountingLLL.ReciprocalTest MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.random_uniform_survival {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (K : α → ℕ) (hK : Measurable K) : (μ.prod (Measure.infinitePi fun i : ℕ => uniformLaw (i+1))) {p : α × ((i : ℕ) → Fin (i+2)) | ∀ i < K p.1, (p.2 i).val ≠ 0} = ∫⁻ x, 1/(K x+1 : ℝ≥0∞) ∂μ := by sorry
