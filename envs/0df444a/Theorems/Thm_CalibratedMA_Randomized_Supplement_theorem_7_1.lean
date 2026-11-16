-- Prove2me | Theorems.Thm_CalibratedMA_Randomized_Supplement_theorem_7_1
-- name    : CalibratedMA.Randomized.Supplement.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:32:45.807989+00:00
-- url     : https://prove2.me/theorems/8483bb79-ce65-42d6-a835-d8380ebe4983
-- title:
--   Theorem 7.1 — Deterministic lower bound with a group budget
-- statement:
--   Let $D$ be the labeled law and $\mathrm{CMA}_D=\max\{\mathrm{MA}_D,\mathrm{ECE}_D\}$ the published error of a full predictor. Probabilities include the iid training sample and an independent training seed; a randomized output may have arbitrary, including continuous, prediction laws.
--
--   There are positive universal $c,c_{\rm size},c_{\rm samp},C_0,a_0,\varepsilon_0$. For every $0<\varepsilon<\varepsilon_0$ and every real budget $A$ with $C_0\log(1/\varepsilon)\le A\le a_0/\varepsilon$, there exist a finite nonempty domain $X_{\varepsilon,A}$, a finite nonempty family $\mathcal D_{\varepsilon,A}$ of Bernoulli-label laws and a finite sign-test family $G_{\varepsilon,A}$ such that
--   $$c_{\rm size}A\le\log|G_{\varepsilon,A}|\le A.$$
--   For every sample count $n$ and every randomized training procedure with deterministic trained output $p$,
--   $$\bigl[\forall D\in\mathcal D_{\varepsilon,A},\
--   \Pr\{\mathrm{CMA}_D(p;G_{\varepsilon,A})\le c\varepsilon\}\ge2/3\bigr]
--   \ \Longrightarrow\ n\ge c_{\rm samp}A^{1/3}\varepsilon^{-8/3}.$$
--   All hard objects are chosen before $n$ and the learner. This is a companion theorem on deterministic prediction, not a step in the proof of Theorem 4.1.
--
--   Differences from the source:
--   - encoding: a finite discrete domain [R] → Fin R, with source coordinate i represented by i.val+1; reason: finite relabeling preserves every statistical experiment, test and error
--   - encoding: labels in [0,1] or in {0,1} → real labels with the corresponding almost-sure support predicate; reason: the measures are the same labeled laws
--   - encoding: a deterministic predictor p → the published CMA or ECE applied to x ↦ dirac(p(x)); reason: the point mass is exactly a deterministic prediction, with no new error measure
--   - encoding: an algorithm using iid examples and independent training randomness → a data-and-seed evaluation map, its product training law, and a measurable success event; reason: this gives the stated ordinary probability and keeps the same algorithm for every unknown distribution; invalid-label inputs can be measurably clipped without affecting any instance
--   - encoding: sufficiently small positive accuracy → one positive universal ε₀ quantified before all instance parameters; reason: the source proof supplies a threshold uniform in the class budget
--   - encoding: finite hard witnesses and both log-cardinality bounds → explicitly nonempty finite witnesses chosen before n and the learner; reason: the source proof constructs these, and the complete budget interval and both inequalities are unchanged
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026; title page November 2, 2026), p. 36, Theorem 7.1 (PDF pp. 38)

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Supplement_Hidden

open MeasureTheory

namespace CalibratedMA.Randomized.Supplement

/-- Theorem 7.1, p.36: the entire real budget interval and both log-cardinality bounds. -/
theorem theorem_7_1 :
    ∃ c csize csamp C₀ a₀ ε₀ : ℝ,
      0 < c ∧ 0 < csize ∧ 0 < csamp ∧ 0 < C₀ ∧ 0 < a₀ ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ A : ℝ,
      C₀ * Real.log (1 / ε) ≤ A → A ≤ a₀ / ε →
      ∃ (R : ℕ) (Ds : Finset (Measure (Fin R × ℝ))) (G : Finset (Fin R → ℝ)),
        0 < R ∧ Ds.Nonempty ∧
        (∀ D ∈ Ds, IsLabeledDist D ∧ ∀ᵐ z ∂D, IsBit z.2) ∧
        (∀ g ∈ G, ∀ i, IsSign (g i)) ∧
        csize * A ≤ Real.log G.card ∧ Real.log G.card ≤ A ∧ G.Nonempty ∧
        ∀ (n : ℕ) (L : DeterministicLearner (Fin R) n),
          (∀ D ∈ Ds, DeterministicSuccess L D G (c * ε) (2 / 3)) →
          (n : ℝ) ≥ csamp * A ^ (1 / 3 : ℝ) / ε ^ (8 / 3 : ℝ) := by sorry

end CalibratedMA.Randomized.Supplement
