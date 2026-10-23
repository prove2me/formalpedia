-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_truncated_convolution_time_primitive
-- name    : AvramDividend.Classical.causal_l1_truncated_convolution_time_primitive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T21:23:20.986093+00:00
-- url     : https://prove2.me/theorems/994301a8-2a6b-4efe-bf7d-3bca912b95d8
-- title:
--   Time-integrated truncated causal convolution as a kernel-primitive integral
-- statement:
--   For a positive-time L1 kernel K and continuous nonnegative-time input g, integrate the truncated two-variable convolution integrand over t∈(0,x]. Fubini swaps the time and lag integrations. The shifted input integral becomes G(x−u) for 0<u≤x and vanishes outside the causal window. This gives the lag integral ∫₀ˣ K(u)G(x−u) du and isolates a key step in the full causal triangle identity.

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_causal_l1_truncated_convolution_fubini_swap
import Theorems.Thm_AvramDividend_Classical_causal_truncated_shift_integral

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_l1_truncated_convolution_time_primitive
    (K g : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (x : ℝ) (hx : 0 < x) :
    (∫ t in Ioc (0 : ℝ) x,
      ∫ u : ℝ,
        ((Ioi (0 : ℝ)).indicator K) u *
        ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume ∂volume) =
    (∫ u in Ioc (0 : ℝ) x,
      K u * (∫ s in Ioc (0 : ℝ) (x - u), g s ∂volume) ∂volume) := by sorry
