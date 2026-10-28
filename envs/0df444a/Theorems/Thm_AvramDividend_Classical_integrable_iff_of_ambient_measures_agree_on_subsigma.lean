-- Prove2me | Theorems.Thm_AvramDividend_Classical_integrable_iff_of_ambient_measures_agree_on_subsigma
-- name    : AvramDividend.Classical.integrable_iff_of_ambient_measures_agree_on_subsigma
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:12:25.841878+00:00
-- url     : https://prove2.me/theorems/731ade82-fc26-449d-84e9-ae38b4112b89
-- title:
--   Integrability transfers between ambient measures that agree on the observable's sigma-algebra
-- statement:
--   For two ambient measurable-space measures that agree on every event of a smaller σ-algebra m, a real random variable f strongly measurable in m is integrable under the first measure if and only if it is integrable under the second. This is needed to transfer known finite Esscher moment integrability from Q_s to a fixed terminal Esscher law Q_T, where Mathlib's discrete martingale constructor requires every grid state to be integrable.
-- source:
--   The ambient measures μ and ν are explicitly typed as `@Measure Ω m0`. Their trimmed measures under m agree by `trim_measurableSet_eq` and measure extensionality. Apply pinned Mathlib `Integrable.trim` and `integrable_of_integrable_trim` to move integrability via the common trimmed measure. This is independent of finite Esscher densities, and it does not assume all Bochner integrals are integrable.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Trim
open MeasureTheory

theorem AvramDividend.Classical.integrable_iff_of_ambient_measures_agree_on_subsigma
    {Ω : Type*} [m0 : MeasurableSpace Ω]
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    (μ ν : @Measure Ω m0)
    (hset : ∀ B : Set Ω, @MeasurableSet Ω m B → μ B = ν B)
    (f : Ω → ℝ) (hf : StronglyMeasurable[m] f) :
    Integrable f μ ↔ Integrable f ν := by sorry
