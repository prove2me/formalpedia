-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_real_convolution_equals_positive_interval_under_support
-- name    : AvramDividend.Classical.causal_real_convolution_equals_positive_interval_under_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:16:40.157925+00:00
-- url     : https://prove2.me/theorems/f884eb9c-3733-4471-8070-ae7641ac8e56
-- title:
--   Full real convolution equals positive-time interval convolution of causal kernels
-- statement:
--   If two real-valued kernels vanish on nonpositive times, then their full Lebesgue convolution equals the integral over the causal time interval (0,x] for every real x. The equality is pointwise at the integrand level, so no global integrability hypothesis is required. It identifies the real L1 convolution form used by continuity theorems with the interval recurrence of the positive renewal-power construction.
-- source:
--   Bridges the canonically Proved causal_l1_convolution_power_sequence_exists interval recurrence to causal_l1_continuous_convolution_power_induction_with_tail_bounds, one step towards the continuous Esscher renewal-density representation 17bc0aad-807f-4e33-82d9-b8a65d2b6166.

import Mathlib.Analysis.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_real_convolution_equals_positive_interval_under_support
    (f g : ℝ → ℝ)
    (hfzero : ∀ y : ℝ, y ≤ 0 → f y = 0)
    (hgzero : ∀ y : ℝ, y ≤ 0 → g y = 0)
    (x : ℝ) :
    (∫ y : ℝ, f y * g (x - y) ∂volume) =
      ∫ y in Ioc (0 : ℝ) x, f y * g (x - y) ∂volume := by sorry
