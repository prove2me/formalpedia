-- Prove2me | Theorems.Thm_CalibratedMA_Randomized_eq_2
-- name    : CalibratedMA.Randomized.eq_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T21:24:40.27661+00:00
-- url     : https://prove2.me/theorems/e2970788-c07f-4ab7-997b-75e5f6ee96e9
-- title:
--   Section 2, Eq. (2) — dual form of the ECE as a supremum over sign tests
-- statement:
--   Let $\mathcal D$ be a distribution on $\mathcal X\times[0,1]$ and $Q$ a randomized predictor, with realized prediction $P\sim Q_X$. Then
--   $$\mathrm{ECE}(Q)=\sup_{h:[0,1]\to\{-1,1\}}\mathbb E[h(P)(Y-P)],\tag{2}$$
--   where $h$ ranges over sign-valued one-dimensional tests of the prediction value.
--
--   The dual form turns calibration into a family of test residuals. Theorem 4.1 uses it with the finitely many sign tests on the support of the rounded predictor.
--
--   **Formalization Note.** The supremum is stated with `IsLUB` over measurable $h:\mathbb R\to\{-1,1\}$. $P\in[0,1]$ almost surely, so only the values of $h$ on $[0,1]$ matter.
--
--   Differences from the source:
--   - encoding: $h:[0,1]\to\{-1,1\}$ arbitrary → $h:\mathbb R\to\{-1,1\}$ measurable; reason: $\mathbb E[h(P)(Y-P)]$ is undefined for non-measurable $h$, and the maximizer $\mathrm{sign}(\mathbb E[Y-P\mid P])$ is a measurable function of $P$, so the supremum is unchanged.
--   - encoding: $\sup$ → `IsLUB`; reason: same value, without the junk value of a real supremum.
--   - encoding: a distribution on X × [0,1] and a randomized predictor → a probability measure D on X × ℝ with Y ∈ [0,1] almost surely and IsRandomizedPredictor Q; reason: the support and measurability conditions give the same joint law and finite expectations.
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026), p. 12, Section 2, Eq. (2)

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Setting

open MeasureTheory

namespace CalibratedMA.Randomized

/-- Section 2, Eq. (2) (p. 12): the expected calibration error is the supremum of the
sign-test residuals `E[h(P)(Y − P)]` over (measurable) `h : [0,1] → {−1, 1}`. -/
theorem eq_2 {X : Type*} [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (hD : ∀ᵐ z ∂D, z.2 ∈ Set.Icc (0 : ℝ) 1) (Q : X → Measure ℝ)
    (hQ : IsRandomizedPredictor Q) :
    IsLUB {v : ℝ | ∃ h : ℝ → ℝ, Measurable h ∧ (∀ p, h p = 1 ∨ h p = -1) ∧
        v = ∫ w, h w.2.2 * (w.2.1 - w.2.2) ∂(jointLaw D Q)} (ECE D Q) := by sorry

end CalibratedMA.Randomized
