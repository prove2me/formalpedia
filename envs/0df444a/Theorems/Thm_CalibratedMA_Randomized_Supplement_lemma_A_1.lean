-- Prove2me | Theorems.Thm_CalibratedMA_Randomized_Supplement_lemma_A_1
-- name    : CalibratedMA.Randomized.Supplement.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:26:47.067639+00:00
-- url     : https://prove2.me/theorems/3a371c6c-293f-41e5-a42e-cedd64277754
-- title:
--   Lemma A.1 — Concentration after category averaging
-- statement:
--   There is a positive universal constant $C$. Fix any context probability law and any Section 5.2 assignment construction with a probability mixture $\pi$. Suppose each nonprivate assignment cell has mass at most $b\ge0$ and every category has score diameter at most $D_{\rm cat}\ge0$, under every assignment. For each measurable $h:X\to[-1,1]$ and every real $t\ge0$,
--   $$\Pr_\omega\{|F_h(\omega)-\mathbb E_\omega F_h(\omega)|>
--    C(\sqrt{b\,\mathbb E_\omega V(\omega)\,t}+bD_{\rm cat}t)\}\le2e^{-t}.$$
--   The category means are recomputed from each assignment. The expectation of $V$, rather than its realized value, occurs in the bound. This concentration result supports Theorem 5.1, with no optimized-parameter or fixed-point hypothesis.
--
--   Differences from the source:
--   - encoding: fixed independent cell assignments with recomputed category means → the same AssignmentConfig and product tuple law, with arbitrary nonnegative mass and score-diameter bounds; reason: retains every instance of the finite construction, including any test mixture, not only the optimized mixture
--   - encoding: a universal C → a positive real C before all types, measures and parameters; reason: makes its uniformity explicit
--   - encoding: only nonprivate cells receive draws → independent unused private-cell draws are integrated out; reason: the residual and its law are unchanged
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026; title page November 2, 2026), p. 47, Lemma A.1 (PDF pp. 49)

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Supplement_Assignment

open MeasureTheory
open scoped ENNReal

namespace CalibratedMA.Randomized.Supplement

/-- Lemma A.1, p.47: C is universal, b and Dcat are arbitrary bounds. -/
theorem lemma_A_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Type) [MeasurableSpace X]
      (P : Measure X), IsProbabilityMeasure P → ∀ (c : AssignmentConfig X)
      (π : Measure (Fin (signedTests c.G).card)), IsProbabilityMeasure π →
      ∀ b Dcat : ℝ, 0 ≤ b → 0 ≤ Dcat → AssignmentMassBound c P b →
        CategoryDiameterBound c Dcat → ∀ h : X → ℝ,
        Measurable h → (∀ x, h x ∈ Set.Icc (-1 : ℝ) 1) → ∀ t : ℝ, 0 ≤ t →
        assignmentLaw c π {ω | |assignmentF c P h ω - meanChange c P π h| >
          C * (Real.sqrt (b * meanVariance c P π * t) + b * Dcat * t)} ≤
          ENNReal.ofReal (2 * Real.exp (-t)) := by sorry

end CalibratedMA.Randomized.Supplement
