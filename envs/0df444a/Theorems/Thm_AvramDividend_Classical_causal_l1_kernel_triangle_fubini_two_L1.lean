-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_triangle_fubini_two_L1
-- name    : AvramDividend.Classical.causal_l1_kernel_triangle_fubini_two_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:24:35.82131+00:00
-- url     : https://prove2.me/theorems/977c5073-8ab6-4000-a28a-50dee91b7b46
-- title:
--   Triangle Fubini for two L1 causal kernels
-- statement:
--   For two potentially singular but locally integrable causal kernels, integrating their convolution over (0,x] equals the convolution of the first kernel with the primitive of the second over that interval. Enables Gaussian signed Neumann convolution-power primitives to satisfy the same Volterra recurrence as the weighted derivative-resolvent series.
-- source:
--   Use the Proved time-reversal and indicator identities and the new two-L1 finite-interval primitive theorem. This is the exact accepted causal_l1_kernel_triangle_fubini proof with the hypothesis ContinuousOn g (Ici 0) relaxed to IntegrableOn g (Ioc 0 x).

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_causal_convolution_time_reversal
import Theorems.Thm_AvramDividend_Classical_causal_open_indicator_inner_identity
import Theorems.Thm_AvramDividend_Classical_causal_l1_truncated_convolution_time_primitive_two_L1

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_l1_kernel_triangle_fubini_two_L1
    (K g : ℝ → ℝ)
    (x : ℝ) (hx : 0 < x)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : IntegrableOn g (Ioc (0 : ℝ) x) volume) :
    (∫ t in Ioc (0 : ℝ) x,
      (∫ s in Ioc (0 : ℝ) t, K (t - s) * g s ∂volume) ∂volume) =
    (∫ s in Ioc (0 : ℝ) x,
      K (x - s) * (∫ t in Ioc (0 : ℝ) s, g t ∂volume) ∂volume) := by sorry
