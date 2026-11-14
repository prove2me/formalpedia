-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_source_cell_drift_bound
-- name    : AvramDividend.Classical.avram_chat24_source_cell_drift_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T21:34:23.561179+00:00
-- url     : https://prove2.me/theorems/68877ca0-2a8f-4927-a6c7-dae4dcbb297b
-- title:
--   Source identity gives the discounted bound on one physical cell
-- statement:
--   Apply the atomic prefix interval identity to identify the cell mass with the sum of nonnegative jump losses. The source algebra and monotone K yield the lower endpoint bound a-d*h, and the two band hypotheses give the upper bound. Apply the discounted Lipschitz chord estimate. The declaration is independent of the grid and ambient measure. Proof depends on the existing atomic prefix lemma and the separately published chord estimate; neither refers back here or to parent 7b52eba8-6fe9-40c9-89f7-a341ca70210b.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_chat24_source_cell_drift_bound
    (f K : ℝ≥0 → ℝ) (v d a b q : ℝ) (B : ℝ≥0)
    (ha : 0 < a) (hd : 0 ≤ d) (hq : 0 ≤ q)
    (hf_down : ∀ t : ℝ≥0, 0 < t → f t ≤ Function.leftLim f t)
    (hK : Monotone K)
    (hsum : Summable (fun r : ℝ≥0 =>
      if 0 < r ∧ r ≤ B then Function.leftLim f r - f r else 0))
    (hsource : ∀ t : ℝ≥0, t ≤ B → f t = (t : ℝ) * d -
      ∑' r : ℝ≥0, if 0 < r ∧ r ≤ t then Function.leftLim f r - f r else 0)
    (s t : ℝ≥0) (hst : s ≤ t) (htB : t ≤ B)
    (hs : v + f s - K s ∈ Icc a b) (ht : v + f t - K t ∈ Icc a b)
    (h m : ℝ) (hh : 0 < h) (hgap : (t : ℝ) - (s : ℝ) = h)
    (hmdef : m = d * h - (f t - f s))
    (hsmall : d * h < min (a / 2) 1)
    (w : ℝ → ℝ) (L : ℝ≥0) (hLip : LipschitzOnWith L w (Icc (a / 2) (b + 1))) :
    ‖Real.exp (-(q * (t : ℝ))) *
      ((w (v + f s - K s + d * h - m) - w (v + f s - K s - m)) / h)‖ ≤
        (L : ℝ) * d := by sorry
