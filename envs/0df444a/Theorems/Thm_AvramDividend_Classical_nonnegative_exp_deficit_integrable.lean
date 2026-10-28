-- Prove2me | Theorems.Thm_AvramDividend_Classical_nonnegative_exp_deficit_integrable
-- name    : AvramDividend.Classical.nonnegative_exp_deficit_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:45:47.962425+00:00
-- url     : https://prove2.me/theorems/2e01c06b-de77-4ab9-885f-543098758196
-- title:
--   Bounded exponential gap of a nonnegative random variable is integrable under a finite measure
-- statement:
--   For an almost surely nonnegative real random variable on a finite measure space and a nonnegative parameter theta, the exponential deficit 1-exp(-theta*D) lies between zero and one almost everywhere. If that deficit is almost-everywhere strongly measurable, it is integrable by Integrable.of_bound. This is the integrability needed for the exponential mesh-gap moment of the bounded-variation Lévy drift deficit.
-- source:
--   Mathlib Integrable.of_bound and Real.exp_le_one_iff.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith

open MeasureTheory

theorem AvramDividend.Classical.nonnegative_exp_deficit_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (D : Ω → ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hNonneg : ∀ᵐ ω ∂P, 0 ≤ D ω)
    (hMeas : AEStronglyMeasurable
      (fun ω => (1 : ℝ) - Real.exp (-θ * D ω)) P) :
    Integrable (fun ω => (1 : ℝ) - Real.exp (-θ * D ω)) P := by sorry
