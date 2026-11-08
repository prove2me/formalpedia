-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_localised_negative_lintegral_tendsto
-- name    : AvramDividend.Classical.avram_bv_residual10_original_localised_negative_lintegral_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:23:34.027507+00:00
-- url     : https://prove2.me/theorems/dce07d06-7a67-44d6-8cfc-6676bfdd0b53
-- title:
--   Extended negative original residual expectation is exhausted by finite coefficient localisation
-- statement:
--   For any measurable real original-process physical-grid residual, the extended Lebesgue expectation of its negative part is the increasing limit of expectations over finite original-row coefficient-bound events. This is valid even when the original residual has no finite L1 norm or its extended expectation is infinite. It supports an alternative to prematurely assuming original generator integrability, but by itself provides no finite mean-zero compensation or L1 convergence.
-- source:
--   AVRAM BV-RESIDUAL10 original physical-grid negative extended expectation and monotone localisation, 7 November 2026

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_measurable

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_bv_residual10_original_localised_negative_lintegral_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (n : ℕ) (a : Ω → ℕ → ℝ)
    (ha : ∀ i, Measurable (fun ω => a ω i))
    (f : Ω → ℝ) (hf : Measurable f) :
    Tendsto
      (fun k : ℕ => ∫⁻ ω, ({z : Ω | ∀ i ∈ Finset.range (n + 1),
        abs (a z i) ≤ (k : ℝ)}).indicator
        (fun z => ENNReal.ofReal (-f z)) ω ∂P)
      atTop (𝓝 (∫⁻ ω, ENNReal.ofReal (-f ω) ∂P)) := by sorry
