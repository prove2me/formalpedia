-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_Ioc_kernel_integral_add
-- name    : AvramDividend.Classical.causal_Ioc_kernel_integral_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T13:51:34.021584+00:00
-- url     : https://prove2.me/theorems/e22751bc-40bf-4a3d-9acb-5128112af53a
-- title:
--   Additivity of an integrable causal Volterra convolution on (0,x]
-- statement:
--   For a real causal kernel B and functions f,g whose products B(x-s)f(s) and B(x-s)g(s) are integrable on (0,x], convolution with the sum f+g is the sum of the two causal convolution integrals. This is the interval-exact operator-additivity input for the finite Neumann telescope.
-- source:
--   Bochner integral additivity on the restricted interval Ioc and pointwise multiplication distribution.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set

theorem AvramDividend.Classical.causal_Ioc_kernel_integral_add
    (B f g : ℝ → ℝ) (x : ℝ)
    (hf : IntegrableOn (fun s : ℝ => B (x - s) * f s)
      (Ioc (0 : ℝ) x) volume)
    (hg : IntegrableOn (fun s : ℝ => B (x - s) * g s)
      (Ioc (0 : ℝ) x) volume) :
    (∫ s in Ioc (0 : ℝ) x, B (x - s) * (f s + g s) ∂volume) =
      (∫ s in Ioc (0 : ℝ) x, B (x - s) * f s ∂volume) +
      (∫ s in Ioc (0 : ℝ) x, B (x - s) * g s ∂volume) := by sorry
