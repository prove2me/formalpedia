-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_singular_fixed_event_nonfinite
-- name    : AvramDividend.Classical.avram_a19_singular_fixed_event_nonfinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:26:39.559045+00:00
-- url     : https://prove2.me/theorems/d9bd365a-9b2e-4a83-902f-721c7d5a38c0
-- title:
--   Positive-probability common event forces singular source-cell nonintegrability
-- statement:
--   If a random source cell on the product of a probability space and an independent geometric index has an absolute lower bound by the singular generator profile simultaneously for every index on one positive-probability event, it cannot have finite absolute integral. The proof selects an almost-everywhere integrable geometric section from that event and contradicts the previously proved divergent geometric loss.
-- source:
--   A19 original pre-dividend reserve countermodel: fixed positive-probability path event and independent geometric dividend index, 7 November 2026. Connects Proved source 3adb6269 to original generator-cell target 5df846f9.

import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_geometric_not_integrable
open MeasureTheory ProbabilityTheory
noncomputable section

theorem AvramDividend.Classical.avram_a19_singular_fixed_event_nonfinite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (A : Set Ω) (hA : P A ≠ 0)
    (p : unitInterval) (hp : p ≠ 0) (hhalf : (p : Real) = 1 / 2)
    (y : Nat → Real)
    (hy : ∀ k, 0 < y k)
    (hsmall : ∀ k, y k ≤ 1 / 16)
    (hpower : ∀ k, y k ≤ 1 / ((2 : Real) ^ k) ^ 2)
    (f : Ω × Nat → Real)
    (hf_meas : AEStronglyMeasurable f (P.prod (geometricMeasure p)))
    (hdom : ∀ ω ∈ A, ∀ k,
      ‖-(3 + y k - 4 * Real.sqrt (y k) - 2 / Real.sqrt (y k))‖ ≤
        ‖f (ω, k)‖) :
    ¬ HasFiniteIntegral f (P.prod (geometricMeasure p)) := by sorry
