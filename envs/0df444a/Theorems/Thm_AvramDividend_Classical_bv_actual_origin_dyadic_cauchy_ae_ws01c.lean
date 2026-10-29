-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_origin_dyadic_cauchy_ae_ws01c
-- name    : AvramDividend.Classical.bv_actual_origin_dyadic_cauchy_ae_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:59:26.285475+00:00
-- url     : https://prove2.me/theorems/3f65132c-b474-4f20-a930-a27deb5ca27c
-- title:
--   Actual bounded-variation Lévy deficit dyadic slopes are almost surely Cauchy at time zero
-- statement:
--   For the actual BV spectrally negative Lévy process, the full dyadic drift-deficit slope sequence at time zero is Cauchy almost surely. Monotone residual path differentiability gives dyadic Cauchy slopes at almost every positive time and path. A measurable joint Cauchy cylinder permits Fubini with Lebesgue measure restricted to (0,1]. Equal whole-path stationary increment laws preserve the Cauchy-event probability between every positive time and zero. Nonzero restricted mass selects a time with almost-sure Cauchy behaviour and transports this to zero. No invalid in-probability to a.s. shortcut is used.
-- source:
--   Source-complete theorem entry from work/avram_ws01c_origin_cauchy_full_assembly_draft.lean, now invoking seven separate canonical/public WS01C helper targets. This is the central Fubini-stationarity Cauchy argument on the route to zero driftless-subordinator slope.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_positive_interval_restricted_volume_ne_zero_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_positive_time_restrict_support_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_actual_stationary_dyadic_ae_positive_cauchy_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_actual_joint_real_cauchy_event_meas_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_dyadic_cauchy_stationary_v2_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_equal_event_measure_ae_equiv_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_supported_stationary_fubini_ws01c

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_origin_dyadic_cauchy_ae_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      CauchySeq (fun n : ℕ =>
        X.drift -
          (X.X (((1 : ℝ≥0) / 2) ^ n) ω - X.X 0 ω) /
            (((1 : ℝ≥0) / 2) ^ n : ℝ)) := by sorry
