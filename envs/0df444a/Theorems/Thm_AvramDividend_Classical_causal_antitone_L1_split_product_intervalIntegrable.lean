-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_antitone_L1_split_product_intervalIntegrable
-- name    : AvramDividend.Classical.causal_antitone_L1_split_product_intervalIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T16:02:33.349582+00:00
-- url     : https://prove2.me/theorems/93dd2fb2-0cd0-4ebb-8ba0-07bccc6666b9
-- title:
--   Positive antitone L1 convolution product is integrable across a midpoint split
-- statement:
--   For a nonnegative antitone continuous L1 causal kernel and a nonnegative L1 input bounded pointwise by A/s, the reflected causal convolution product κ(x−s)F(s) is integrable over every positive-time interval (0,x]. The proof splits at x/2, where the nonsingular factor is bounded on each side.
-- source:
--   Choose x/2, use global L1 to restrict F left of the split, continuous positive-time κ for reflected measurability, L1 reflection for κ right of the split, and the Proved cutoff product integrability theorem. Glue the two interval-integrable pieces with IntervalIntegrable.trans. This supplies hFint for the signed Gaussian power majorant.

import Mathlib.Analysis.Convolution
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_causal_positive_L1_intervalIntegrable
import Theorems.Thm_AvramDividend_Classical_causal_reflected_kernel_right_interval_integrable
import Theorems.Thm_AvramDividend_Classical_causal_antitone_split_product_integrable_of_pointwise_bound

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_antitone_L1_split_product_intervalIntegrable
    (κ F : ℝ → ℝ) (x A : ℝ) (hx : 0 < x) (hA : 0 ≤ A)
    (hκanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hκnonneg : ∀ t : ℝ, 0 < t → 0 ≤ κ t)
    (hκL1 : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hFnonneg : ∀ s : ℝ, 0 < s → 0 ≤ F s)
    (hFpoint : ∀ s : ℝ, 0 < s → F s ≤ A / s)
    (hFL1 : IntegrableOn F (Ioi (0 : ℝ)) volume) :
    IntervalIntegrable (fun s : ℝ => κ (x - s) * F s) volume 0 x := by sorry
