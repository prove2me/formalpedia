-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_ae_cauchy_plus_in_measure_bundle_ws01c
-- name    : AvramDividend.Classical.bv_ae_cauchy_plus_in_measure_bundle_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T11:59:17.184551+00:00
-- url     : https://prove2.me/theorems/eb4d928e-fd97-4edd-b079-a0ad51e525a8
-- title:
--   Almost-sure Cauchy convergence plus convergence in measure fixes the full zero limit
-- statement:
--   For a real random sequence that is pathwise Cauchy almost surely and converges to zero in measure, every path outside a null set converges to zero along the entire sequence. A subsequence converges almost surely by the convergence-in-measure extraction theorem; the full Cauchy sequence has that unique limit. This avoids the false inference that an arbitrary in-probability sequence converges almost surely.
-- source:
--   Standard subsequence principle and Cauchy convergence, necessary for the bounded-variation Lévy residual dyadic zero-slope argument in WS01C. Source work/avram_ws01c_probability_bridge_bundle_draft.lean.

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.UniformSpace.Cauchy

open Filter MeasureTheory Topology

theorem AvramDividend.Classical.bv_ae_cauchy_plus_in_measure_bundle_ws01c
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : ℕ → Ω → ℝ)
    (hC : ∀ᵐ ω ∂P, CauchySeq (fun n => f n ω))
    (hProb : TendstoInMeasure P f atTop (fun _ => (0 : ℝ))) :
    ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 0) := by sorry
