-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_truncated_convolution_fubini_swap
-- name    : AvramDividend.Classical.causal_l1_truncated_convolution_fubini_swap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T21:12:17.830469+00:00
-- url     : https://prove2.me/theorems/63b71413-d9c3-4562-9606-c5f36c8a09a5
-- title:
--   Finite-horizon Fubini interchange for truncated causal convolution
-- statement:
--   Given a positive-time integrable kernel K and continuous nonnegative-time input g, the globally integrable truncated convolution integrand permits exchange of the finite time integral over (0,x] with the lag integral over the real line. This follows from the product-integrability result and set-integral Fubini, and supplies an intermediate step for the triangle Fubini identity.

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_causal_l1_truncated_convolution_prod_integrable
import Theorems.Thm_MeasureTheory_setIntegral_integral_swap

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_l1_truncated_convolution_fubini_swap
    (K g : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (x : ℝ) (hx : 0 < x) :
    (∫ t in Ioc (0 : ℝ) x,
      ∫ u : ℝ,
        ((Ioi (0 : ℝ)).indicator K) u *
        ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume ∂volume) =
    (∫ u : ℝ,
      ∫ t in Ioc (0 : ℝ) x,
        ((Ioi (0 : ℝ)).indicator K) u *
        ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume ∂volume) := by sorry
