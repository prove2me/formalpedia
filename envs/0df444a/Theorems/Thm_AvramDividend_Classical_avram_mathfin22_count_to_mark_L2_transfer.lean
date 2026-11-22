-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mathfin22_count_to_mark_L2_transfer
-- name    : AvramDividend.Classical.avram_mathfin22_count_to_mark_L2_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:40:54.494567+00:00
-- url     : https://prove2.me/theorems/3ae6f40f-4400-414d-923e-e6c028a7d56a
-- title:
--   Square integrability transfer from centred original jump-count second moment to bounded compensated mark
-- statement:
--   A minimal deterministic-measure-theory transfer needed for the original physical Lévy signed-mark integral. If actual finite mark-band count N has an integrable centred square and J is an integrable signed mark dominated almost surely by N+|d| for deterministic compensator d, then J has an integrable square. It supplies no stochastic axiom, independently scattered random measure or new filtration. The original X count moments and pathwise domination will be supplied by existing Proved physical-source theorems in the parent.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
open MeasureTheory Set
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mathfin22_count_to_mark_L2_transfer
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (J N : Ω → ℝ) (r d : ℝ)
    (hJ : Integrable J P) (hN : Integrable N P)
    (hNcenter : Integrable (fun ω => (N ω - r) ^ 2) P)
    (hBound : ∀ᵐ ω ∂P, |J ω| ≤ N ω + |d|) :
    Integrable (fun ω => (J ω) ^ 2) P := by sorry
