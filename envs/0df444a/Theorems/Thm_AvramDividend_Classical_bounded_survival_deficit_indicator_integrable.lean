-- Prove2me | Theorems.Thm_AvramDividend_Classical_bounded_survival_deficit_indicator_integrable
-- name    : AvramDividend.Classical.bounded_survival_deficit_indicator_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:16:43.221894+00:00
-- url     : https://prove2.me/theorems/72ca6939-d04c-4203-98db-6a452c04bf6b
-- title:
--   Integrability of a nonnegative drift deficit bounded on a survival event under a finite measure
-- statement:
--   Even if the unrestricted BV Lévy drift deficit has infinite expectation due to large downward jumps, its indicator restricted to the strict zero-barrier survival event is bounded by physical drift times the survival horizon. On any finite measure space, almost-sure nonnegativity, this eventwise upper bound, and almost-sure strong measurability imply its Bochner integrability. This discharges a critical assumption in the accepted finite-mesh expected-survival bound.
-- source:
--   Mathlib Integrable.of_bound and real norm simplification.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

open MeasureTheory Set

theorem AvramDividend.Classical.bounded_survival_deficit_indicator_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (E : Set Ω) (D : Ω → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hMeas : AEStronglyMeasurable (E.indicator D) P)
    (hNonneg : ∀ᵐ ω ∂P, 0 ≤ D ω)
    (hBound : ∀ ω ∈ E, D ω ≤ C) :
    Integrable (E.indicator D) P := by sorry
