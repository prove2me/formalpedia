-- Prove2me | Theorems.Thm_CalibratedMA_Randomized_Supplement_lemma_6_3
-- name    : CalibratedMA.Randomized.Supplement.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:28:41.067208+00:00
-- url     : https://prove2.me/theorems/47685cf7-9248-4f89-ac7b-48718c005a83
-- title:
--   Lemma 6.3 — Finite-class multiaccuracy lower bound
-- statement:
--   Let $D$ be the labeled law and $\mathrm{CMA}_D=\max\{\mathrm{MA}_D,\mathrm{ECE}_D\}$ the published error of a full predictor. Probabilities include the iid training sample and an independent training seed; a randomized output may have arbitrary, including continuous, prediction laws.
--
--   There are positive universal $c,c_0,\varepsilon_0$. For every integer $N_G\ge2$ and $0<\varepsilon<\varepsilon_0$, there are a finite nonempty domain $X_0$, a nonempty sign-test family $G_0\subseteq\{-1,1\}^{X_0}$ of size at most $N_G$, and a finite nonempty family $\mathcal D_0$ of Bernoulli-label laws such that every learner obeys
--   $$\bigl[\forall D\in\mathcal D_0,\ \Pr\{\mathrm{CMA}_D(Q;G_0)\le c\varepsilon\}\ge2/3\bigr]
--   \ \Longrightarrow\ n\ge c_0\log(N_G)/\varepsilon^2.$$
--   The domain, tests and hard family are fixed before the sample count and arbitrary learner. This supplies the finite-class component of Theorem 6.1; its attribution is retained in the milestone provenance.
--
--   Differences from the source:
--   - encoding: a finite discrete domain [R] → Fin R, with source coordinate i represented by i.val+1; reason: finite relabeling preserves every statistical experiment, test and error
--   - encoding: labels in [0,1] or in {0,1} → real labels with the corresponding almost-sure support predicate; reason: the measures are the same labeled laws
--   - encoding: an algorithm using iid examples and independent training randomness → a data-and-seed evaluation map, its product training law, and a measurable success event; reason: this gives the stated ordinary probability and keeps the same algorithm for every unknown distribution; invalid-label inputs can be measurably clipped without affecting any instance
--   - encoding: sufficiently small positive accuracy → one positive universal ε₀ quantified before all instance parameters; reason: the source proof supplies a threshold uniform in the class budget
--   - encoding: finite hard domain, tests and family of laws → nonempty finite witnesses; reason: the proof constructs such witnesses; emptiness supplies no source hard instance
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026; title page November 2, 2026), p. 33, Lemma 6.3 (PDF pp. 35)

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Supplement_Hidden

open MeasureTheory

namespace CalibratedMA.Randomized.Supplement

/-- Lemma 6.3, p.33: a single finite hard family is chosen before n and the learner. -/
theorem lemma_6_3 :
    ∃ c c₀ ε₀ : ℝ, 0 < c ∧ 0 < c₀ ∧ 0 < ε₀ ∧
      ∀ NG : ℕ, 2 ≤ NG → ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ (R : ℕ) (G : Finset (Fin R → ℝ)) (Ds : Finset (Measure (Fin R × ℝ))),
        0 < R ∧ G.Nonempty ∧ G.card ≤ NG ∧
        (∀ g ∈ G, ∀ i, IsSign (g i)) ∧ Ds.Nonempty ∧
        (∀ D ∈ Ds, IsLabeledDist D ∧ ∀ᵐ z ∂D, IsBit z.2) ∧
        ∀ (n : ℕ) (L : RandomizedLearner (Fin R) n),
          (∀ D ∈ Ds, RandomizedSuccess L D G (c * ε) (2 / 3)) →
          (n : ℝ) ≥ c₀ * Real.log NG / ε ^ 2 := by sorry

end CalibratedMA.Randomized.Supplement
