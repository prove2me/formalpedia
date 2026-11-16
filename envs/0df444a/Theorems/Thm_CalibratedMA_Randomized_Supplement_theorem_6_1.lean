-- Prove2me | Theorems.Thm_CalibratedMA_Randomized_Supplement_theorem_6_1
-- name    : CalibratedMA.Randomized.Supplement.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:30:47.66319+00:00
-- url     : https://prove2.me/theorems/c76a412a-6493-4b06-99cd-b8abf22a6d94
-- title:
--   Theorem 6.1 — Matching lower bound for randomized predictors
-- statement:
--   Let $D$ be the labeled law and $\mathrm{CMA}_D=\max\{\mathrm{MA}_D,\mathrm{ECE}_D\}$ the published error of a full predictor. Probabilities include the iid training sample and an independent training seed; a randomized output may have arbitrary, including continuous, prediction laws.
--
--   There are positive universal $c,c_0,\varepsilon_0$. For every integer $N_G\ge2$ and every $0<\varepsilon<\varepsilon_0$, suppose one learner family with common sample count $n$ has the following guarantee for every finite discrete domain $X$, every finite bounded test family $G\subseteq[-1,1]^X$ with $|G|\le N_G$, and every labeled law $D$ on $X\times[0,1]$:
--   $$\Pr\{\mathrm{CMA}_D(Q;G)\le c\varepsilon\}\ge2/3.$$
--   Then the full sum lower bound holds:
--   $$n\ge c_0\left(\frac{\log N_G}{\varepsilon^2}+\frac1{\varepsilon^{5/2}}\right).$$
--   The learner may depend on the public domain and tests but cannot depend on $D$. This companion theorem matches the two randomized rates; it is not used in the proof of Theorem 4.1.
--
--   Differences from the source:
--   - encoding: a finite discrete domain [R] → Fin R, with source coordinate i represented by i.val+1; reason: finite relabeling preserves every statistical experiment, test and error
--   - encoding: labels in [0,1] or in {0,1} → real labels with the corresponding almost-sure support predicate; reason: the measures are the same labeled laws
--   - encoding: an algorithm using iid examples and independent training randomness → a data-and-seed evaluation map, its product training law, and a measurable success event; reason: this gives the stated ordinary probability and keeps the same algorithm for every unknown distribution; invalid-label inputs can be measurably clipped without affecting any instance
--   - encoding: sufficiently small positive accuracy → one positive universal ε₀ quantified before all instance parameters; reason: the source proof supplies a threshold uniform in the class budget
--   - encoding: one algorithm uniform over finite domains and public test families → one dependent family L R G with common n, chosen before all distributions; reason: finite discrete relabeling preserves all guarantees and permits different public-parameter seed laws
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026; title page November 2, 2026), p. 32, Theorem 6.1 (PDF pp. 34)

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Supplement_Hidden

open MeasureTheory

namespace CalibratedMA.Randomized.Supplement

/-- Theorem 6.1, p.32: finite domains are represented by their cardinality and relabeling. -/
theorem theorem_6_1 :
    ∃ c c₀ ε₀ : ℝ, 0 < c ∧ 0 < c₀ ∧ 0 < ε₀ ∧
      ∀ NG : ℕ, 2 ≤ NG → ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (n : ℕ) (L : ∀ R : ℕ, Finset (Fin R → ℝ) → RandomizedLearner (Fin R) n),
        (∀ (R : ℕ) (G : Finset (Fin R → ℝ)), G.card ≤ NG →
          (∀ g ∈ G, ∀ i, g i ∈ Set.Icc (-1 : ℝ) 1) →
          ∀ D : Measure (Fin R × ℝ), IsLabeledDist D →
            RandomizedSuccess (L R G) D G (c * ε) (2 / 3)) →
        (n : ℝ) ≥ c₀ * (Real.log NG / ε ^ 2 + 1 / ε ^ (5 / 2 : ℝ)) := by sorry

end CalibratedMA.Randomized.Supplement
