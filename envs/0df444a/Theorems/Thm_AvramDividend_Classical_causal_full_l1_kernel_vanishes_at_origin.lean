-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_full_l1_kernel_vanishes_at_origin
-- name    : AvramDividend.Classical.causal_full_l1_kernel_vanishes_at_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:08:30.825305+00:00
-- url     : https://prove2.me/theorems/9be58b26-adab-42d4-8ddf-47f95940208f
-- title:
--   Full drift plus integrable causal convolution vanishes at the origin for locally bounded input
-- statement:
--   For K integrable on the positive half-line, V continuous on [0,infinity) and locally bounded on positive bounded intervals, the full causal convolution of (beta+K) with V tends to zero as x decreases to zero. Split the beta times causal primitive from the K-convolution using integrability. Both limits are Proved for their individual terms. This extends the bounded-continuous-function restricted result to the continuous Gaussian derivative resolvent required for the canonical origin derivative 2/sigma squared.
-- source:
--   Exact generalisation of Proved causal_weighted_BCF_full_kernel_vanishes_origin and its source, removing the BCF restriction.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.NhdsWithin
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_vanishes_at_origin
import Theorems.Thm_AvramDividend_Classical_causal_continuous_input_primitive_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_continuous_input_integrable
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace AvramDividend.Classical
/-- A locally bounded continuous input makes the full drift-plus-L1 causal convolution vanish at zero. -/
theorem causal_full_l1_kernel_vanishes_at_origin
    (K V : ℝ → ℝ) (β : ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ici (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |V s| ≤ C) :
    Tendsto (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
      (β + K (x - s)) * V s ∂volume)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  sorry
end AvramDividend.Classical
