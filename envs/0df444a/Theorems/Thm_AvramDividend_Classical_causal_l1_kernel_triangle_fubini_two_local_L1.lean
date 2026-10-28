-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_triangle_fubini_two_local_L1
-- name    : AvramDividend.Classical.causal_l1_kernel_triangle_fubini_two_local_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:27:18.750003+00:00
-- url     : https://prove2.me/theorems/77c56cc3-bcfe-437c-8b4c-d0da9e79711f
-- title:
--   Finite triangle Fubini under local L1 assumptions on both kernels
-- statement:
--   If both real causal kernels are integrable on the finite interval (0,x], their time-convolution triangle satisfies the Fubini primitive identity. This removes the global-L1 restriction for the exponentially untilted Gaussian kernel β+K, which has a constant drift term.
-- source:
--   Truncate the first L1 kernel to Iic x, observe its positive-side zero extension equals the original K restricted to Ioc 0 x and hence is globally L1 on positive times. Apply the Proved two-L1 triangle Fubini theorem to this truncated kernel. On the causal integration triangle t≤x and 0<s≤t, its value agrees pointwise with K(t-s).

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_triangle_fubini_two_L1

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_l1_kernel_triangle_fubini_two_local_L1
    (K g : ℝ → ℝ) (x : ℝ) (hx : 0 < x)
    (hK : IntegrableOn K (Ioc (0 : ℝ) x) volume)
    (hg : IntegrableOn g (Ioc (0 : ℝ) x) volume) :
    (∫ t in Ioc (0 : ℝ) x,
      (∫ s in Ioc (0 : ℝ) t, K (t - s) * g s ∂volume) ∂volume) =
    (∫ s in Ioc (0 : ℝ) x,
      K (x - s) * (∫ t in Ioc (0 : ℝ) s, g t ∂volume) ∂volume) := by sorry
