-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_discounted_drift_chord_bound
-- name    : AvramDividend.Classical.avram_chat24_discounted_drift_chord_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T21:25:49.617888+00:00
-- url     : https://prove2.me/theorems/e67bb430-4f3c-4d71-a325-79963f85820f
-- title:
--   Discounted Lipschitz bound for one drift chord
-- statement:
--   Local analytic estimate for parent 7b52eba8-6fe9-40c9-89f7-a341ca70210b. The lower endpoint bound a-d*h<=x-m and d*h<min(a/2,1) place both endpoints in the Lipschitz band. Divide the Lipschitz bound by positive h and use exp(-q*t)<=1. Full proof draft is preserved in p2m-drift-chord-bound-research.lean. This theorem has no platform dependencies and does not refer to its parent.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_chat24_discounted_drift_chord_bound
    (w : ℝ → ℝ) (L : ℝ≥0) (a b x m d h q t : ℝ)
    (ha : 0 < a) (hd : 0 ≤ d) (hh : 0 < h)
    (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hx : x ∈ Icc a b) (hm : 0 ≤ m)
    (hlow : a - d * h ≤ x - m)
    (hsmall : d * h < min (a / 2) 1)
    (hLip : LipschitzOnWith L w (Icc (a / 2) (b + 1))) :
    ‖Real.exp (-(q * t)) *
      ((w (x + d * h - m) - w (x - m)) / h)‖ ≤ (L : ℝ) * d := by sorry
