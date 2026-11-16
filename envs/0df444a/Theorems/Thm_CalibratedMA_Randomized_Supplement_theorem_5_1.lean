-- Prove2me | Theorems.Thm_CalibratedMA_Randomized_Supplement_theorem_5_1
-- name    : CalibratedMA.Randomized.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:27:22.583645+00:00
-- url     : https://prove2.me/theorems/d437072d-ee67-4f7e-8e92-84835a3d08ea
-- title:
--   Theorem 5.1 — Deterministic upper bound
-- statement:
--   Let $D$ be the labeled law and $\mathrm{CMA}_D=\max\{\mathrm{MA}_D,\mathrm{ECE}_D\}$ the published error of a full predictor. Probabilities include the iid training sample and an independent training seed; a randomized output may have arbitrary, including continuous, prediction laws.
--
--   There is a universal $C\ge e$ such that the following holds in every finite dimension $d$. Let $X$ be any Borel subset of $[0,1]^d$ and $G$ a nonempty finite family of measurable $[-1,1]$-valued tests. For every $\varepsilon,\delta\in(0,1/10)$ and every sample count $n$ satisfying
--   $$n\ge\left\lceil C\left(\frac{A}{\varepsilon^2}+\frac{A^{1/3}}{\varepsilon^{8/3}}\right)\log\frac{CB}{\varepsilon\delta}\right\rceil,
--   \quad A=\log(8|G|/\delta)+1,\quad B=A+(A/\varepsilon^2)^{1/3},$$
--   there is a learner chosen before $D$, valid for every probability law $D$ on $X\times[0,1]$, whose trained output is a deterministic measurable function $p:X\to[0,1]$ and satisfies
--   $$\Pr\{\mathrm{CMA}_D(p;G)\le\varepsilon\}\ge1-\delta.$$
--   There is no assumption of finite support, atomlessness, or computational efficiency. This is a companion theorem, not a step in the proof of Theorem 4.1. The displayed logarithm makes the source's sample bound explicit.
--
--   Differences from the source:
--   - encoding: labels in [0,1] or in {0,1} → real labels with the corresponding almost-sure support predicate; reason: the measures are the same labeled laws
--   - encoding: a deterministic predictor p → the published CMA or ECE applied to x ↦ dirac(p(x)); reason: the point mass is exactly a deterministic prediction, with no new error measure
--   - encoding: an algorithm using iid examples and independent training randomness → a data-and-seed evaluation map, its product training law, and a measurable success event; reason: this gives the stated ordinary probability and keeps the same algorithm for every unknown distribution; invalid-label inputs can be measurably clipped without affecting any instance
--   - encoding: any Borel subset of the d-dimensional unit cube → a measurable subset of Fin d → ℝ contained in the coordinatewise unit cube; reason: the inherited product Borel space and subtype have the same instances
--   - encoding: Õ(A/ε²+A^(1/3)/ε^(8/3)) samples → the displayed ceiling envelope with B=A+(A/ε²)^(1/3), a universal C≥e, and all larger n; reason: Algorithm 2 and Appendix A Eq. (27), including the large-budget branch, give this logarithm; extra examples may be ignored
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026; title page November 2, 2026), p. 21, Theorem 5.1 (PDF pp. 23)

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Supplement_Learning

open MeasureTheory

namespace CalibratedMA.Randomized.Supplement

/-- Theorem 5.1, p.21, with the logarithmic envelope supplied by Algorithm 2 and Eq. (27).
The learner is chosen before the unknown data distribution. -/
theorem theorem_5_1 :
    ∃ C : ℝ, Real.exp 1 ≤ C ∧ ∀ (d : ℕ) (X : Set (Fin d → ℝ)),
      MeasurableSet X → (∀ x ∈ X, ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ G : Finset (X → ℝ), G.Nonempty →
        (∀ g ∈ G, Measurable g ∧ ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1) →
      ∀ ε δ : ℝ, 0 < ε → ε < 1 / 10 → 0 < δ → δ < 1 / 10 →
      ∀ n : ℕ, deterministicSampleBound C ε δ G.card ≤ n →
      ∃ L : DeterministicLearner X n, ∀ D : Measure (X × ℝ),
        IsLabeledDist D → DeterministicSuccess L D G ε (1 - δ) := by sorry

end CalibratedMA.Randomized.Supplement
