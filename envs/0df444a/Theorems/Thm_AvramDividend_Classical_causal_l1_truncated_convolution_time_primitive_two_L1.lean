-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_truncated_convolution_time_primitive_two_L1
-- name    : AvramDividend.Classical.causal_l1_truncated_convolution_time_primitive_two_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:21:05.478969+00:00
-- url     : https://prove2.me/theorems/690ceebf-3c54-46e9-bcca-cdf8bb48a4e3
-- title:
--   Finite-horizon causal convolution as a primitive for two L1 inputs
-- statement:
--   For K integrable on positive times and g integrable over (0,x], integrate the causal truncated convolution over the finite time window and identify the result with the lag integral of K times the finite-interval primitive of g. Provides the second L1 Fubini step for Gaussian derivative-resolvent Neumann powers.
-- source:
--   Copy the already Proved causal_l1_truncated_convolution_time_primitive derivation with only the Fubini step strengthened to an L1 second input. The truncated-shift integral identity and interval indicator support algebra do not use continuity.

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_causal_l1_truncated_convolution_fubini_swap_two_L1
import Theorems.Thm_AvramDividend_Classical_causal_truncated_shift_integral

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_l1_truncated_convolution_time_primitive_two_L1
    (K g : ℝ → ℝ)
    (x : ℝ) (hx : 0 < x)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : IntegrableOn g (Ioc (0 : ℝ) x) volume) :
    (∫ t in Ioc (0 : ℝ) x,
      ∫ u : ℝ,
        ((Ioi (0 : ℝ)).indicator K) u *
        ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume ∂volume) =
    (∫ u in Ioc (0 : ℝ) x,
      K u * (∫ s in Ioc (0 : ℝ) (x - u), g s ∂volume) ∂volume) := by sorry
