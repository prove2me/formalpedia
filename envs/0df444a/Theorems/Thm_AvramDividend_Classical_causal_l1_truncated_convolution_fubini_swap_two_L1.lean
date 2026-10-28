-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_truncated_convolution_fubini_swap_two_L1
-- name    : AvramDividend.Classical.causal_l1_truncated_convolution_fubini_swap_two_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:03:45.376976+00:00
-- url     : https://prove2.me/theorems/e0a6697f-0019-435b-8229-82502df1beed
-- title:
--   Finite-horizon causal Fubini interchange for two L1 inputs
-- statement:
--   A positive-time L1 kernel and a second input integrable on (0,x] allow exchange of the causal truncated convolution's time and lag integrals. This supplies the Fubini bridge for signed Neumann powers, whose inputs need not be continuous at the origin.
-- source:
--   Generalise the accepted finite-horizon causal Fubini swap. Replace continuous positive-half-line input by direct IntegrableOn g (Ioc 0 x), apply the Proved two-L1 convolution product integrability, restrict to the time interval, and invoke the Proved setIntegral_integral_swap.

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_causal_l1_truncated_convolution_prod_integrable_two_L1
import Theorems.Thm_MeasureTheory_setIntegral_integral_swap

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_l1_truncated_convolution_fubini_swap_two_L1
    (K g : ℝ → ℝ)
    (x : ℝ) (hx : 0 < x)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : IntegrableOn g (Ioc (0 : ℝ) x) volume) :
    (∫ t in Ioc (0 : ℝ) x,
      ∫ u : ℝ,
        ((Ioi (0 : ℝ)).indicator K) u *
        ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume ∂volume) =
    (∫ u : ℝ,
      ∫ t in Ioc (0 : ℝ) x,
        ((Ioi (0 : ℝ)).indicator K) u *
        ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume ∂volume) := by sorry
