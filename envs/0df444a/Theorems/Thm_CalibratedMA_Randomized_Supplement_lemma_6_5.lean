-- Prove2me | Theorems.Thm_CalibratedMA_Randomized_Supplement_lemma_6_5
-- name    : CalibratedMA.Randomized.Supplement.lemma_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:29:51.138203+00:00
-- url     : https://prove2.me/theorems/857ebffb-9a29-4dda-9f01-7dd2ddf0e010
-- title:
--   Lemma 6.5 — Calibration lower bound for randomized predictors
-- statement:
--   Let $D$ be the labeled law and $\mathrm{CMA}_D=\max\{\mathrm{MA}_D,\mathrm{ECE}_D\}$ the published error of a full predictor. Probabilities include the iid training sample and an independent training seed; a randomized output may have arbitrary, including continuous, prediction laws.
--
--   There are positive universal $c,c_0,\varepsilon_0$. For every $0<\varepsilon<\varepsilon_0$ there is a finite nonempty subset $X_\varepsilon\subseteq[0,1]$ such that every learner with arbitrary randomized output satisfies
--   $$\bigl[\forall D\text{ on }X_\varepsilon\times\{0,1\},\
--   \Pr\{\mathrm{CMA}_D(Q;\{x\mapsto x\})\le c\varepsilon\}\ge2/3\bigr]
--   \ \Longrightarrow\ n\ge c_0\varepsilon^{-5/2}.$$
--   The lower bound already uses the singleton identity test. The finite domain is chosen before the learner and its sample count. This is the calibration component of Theorem 6.1.
--
--   Differences from the source:
--   - encoding: labels in [0,1] or in {0,1} → real labels with the corresponding almost-sure support predicate; reason: the measures are the same labeled laws
--   - encoding: an algorithm using iid examples and independent training randomness → a data-and-seed evaluation map, its product training law, and a measurable success event; reason: this gives the stated ordinary probability and keeps the same algorithm for every unknown distribution; invalid-label inputs can be measurably clipped without affecting any instance
--   - encoding: sufficiently small positive accuracy → one positive universal ε₀ quantified before all instance parameters; reason: the source proof supplies a threshold uniform in the class budget
--   - encoding: a finite subset of [0,1] → a nonempty Finset ℝ and its subtype, with the identity test; reason: the subtype keeps the actual coordinates and all Bernoulli-label probability laws
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026; title page November 2, 2026), p. 35, Lemma 6.5 (PDF pp. 37)

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Supplement_Hidden

open MeasureTheory

namespace CalibratedMA.Randomized.Supplement

/-- Lemma 6.5, p.35: every Bernoulli-label law on the chosen finite subset of [0,1]. -/
theorem lemma_6_5 :
    ∃ c c₀ ε₀ : ℝ, 0 < c ∧ 0 < c₀ ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ T : Finset ℝ, T.Nonempty ∧ (∀ x ∈ T, x ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ (n : ℕ) (L : RandomizedLearner T n),
          (∀ D : Measure (T × ℝ), IsLabeledDist D → (∀ᵐ z ∂D, IsBit z.2) →
            RandomizedSuccess L D {fun x : T => (x : ℝ)} (c * ε) (2 / 3)) →
          (n : ℝ) ≥ c₀ / ε ^ (5 / 2 : ℝ) := by sorry

end CalibratedMA.Randomized.Supplement
