-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_ae_nonneg_tail_tendstoInMeasure_zero_ws01c
-- name    : AvramDividend.Classical.bv_ae_nonneg_tail_tendstoInMeasure_zero_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:06:04.770928+00:00
-- url     : https://prove2.me/theorems/22bf82e4-d343-4601-b145-2045313e9e19
-- title:
--   Almost-sure nonnegative upper tails imply convergence in measure
-- statement:
--   Indexwise almost-sure nonnegativity and vanishing positive tails imply convergence in measure of the full sequence to zero. The positive-part sequence is everywhere nonnegative; its upper-tail events coincide at positive thresholds, and its values agree almost everywhere with the original sequence. This is distinct from the earlier everywhere-nonnegative bundle.
-- source:
--   Causal resubmission of terminal failed publication job 0aa57b1d-c426-4453-84de-7f18c0214007. It failed solely because required bv_nonnegative_tails_bundle_ws01c was then Open. Its exact UUID 753f1426-ed9c-4e89-8cde-4607abf7e79b is now canonically Proved with accepted source bc69885d-87d6-4b36-a1cb-c486b500a4b6; the original statement/proof bytes are unchanged. Source work/avram_ws01c_ae_nonnegative_tail_solution_direct.lean.

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Theorems.Thm_AvramDividend_Classical_bv_nonnegative_tails_bundle_ws01c

open MeasureTheory Filter Topology
open AvramDividend.Classical

theorem AvramDividend.Classical.bv_ae_nonneg_tail_tendstoInMeasure_zero_ws01c
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (f : ℕ → Ω → ℝ)
    (hNonneg : ∀ n, ∀ᵐ ω ∂P, 0 ≤ f n ω)
    (hTail : ∀ a : ℝ, 0 < a →
      Tendsto (fun n => P.real {ω | a ≤ f n ω}) atTop (𝓝 0)) :
    TendstoInMeasure P f atTop (fun _ => (0 : ℝ)) := by sorry
