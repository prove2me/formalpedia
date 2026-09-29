-- Prove2me | Theorems.Thm_FamousTheorems_probability_measure_determined_by_cdf_7a
-- name    : FamousTheorems.probability_measure_determined_by_cdf_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:23.635803+00:00
-- url     : https://prove2.me/theorems/5be9cc40-0a4c-4a3b-8a90-152ba122d20f
-- title:
--   A probability measure on ℝ is determined by its CDF
-- statement:
--   **A probability measure on $\mathbb R$ is determined by its CDF.** Let $\mu,\nu$ be probability measures on $\mathbb R$ with the same cumulative distribution function, $\mu(-\infty,x]=\nu(-\infty,x]$ for every $x\in\mathbb R$. Then $\mu=\nu$.
--
--   The half-lines $(-\infty,x]$ form a $\pi$-system that generates the Borel $\sigma$-algebra, so the result follows from Dynkin's $\pi$–$\lambda$ theorem. Together with the converse, that every non-decreasing right-continuous function with limits $0$ and $1$ is a CDF, it identifies probability measures on $\mathbb R$ with distribution functions. This is how distributions are specified in elementary probability.
--
--   **Formalization note.** Mathlib's `MeasureTheory.Measure.eq_of_cdf`. `ProbabilityTheory.cdf μ` is the function $x\mapsto\mu(-\infty,x]$, as a bundled Stieltjes function.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.Measure.eq_of_cdf`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem probability_measure_determined_by_cdf_7a (μ ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν]
    (h : ProbabilityTheory.cdf μ = ProbabilityTheory.cdf ν) : μ = ν := by sorry

end FamousTheorems
