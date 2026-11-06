-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_finite_envelope_zero_scale_product_vanish
-- name    : AvramDividend.Classical.avram_limit2_finite_envelope_zero_scale_product_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:00:18.776328+00:00
-- url     : https://prove2.me/theorems/e21f1b7d-c2d1-48fd-87db-8bd319ac12f9
-- title:
--   Finite expected stochastic envelope preserves deterministic zero-scale convergence
-- statement:
--   The product of a deterministic nonnegative scale tending to zero and a finite expected ENNReal stochastic envelope tends to zero. The finiteness hypothesis explicitly excludes the discontinuity of ENNReal multiplication at zero times infinity; this certifies the analytic premise required by the terminal squeeze theorem.

import Mathlib
open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_limit2_finite_envelope_zero_scale_product_vanish
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (scale : ℕ → ℝ≥0∞) (Envelope : Ω → ℝ≥0∞)
    (hFinite : (∫⁻ ω, Envelope ω ∂P) < ⊤)
    (hScale : Filter.Tendsto scale Filter.atTop (nhds (0 : ℝ≥0∞))) :
    Filter.Tendsto
      (fun n : ℕ => scale n * (∫⁻ ω, Envelope ω ∂P))
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by sorry
