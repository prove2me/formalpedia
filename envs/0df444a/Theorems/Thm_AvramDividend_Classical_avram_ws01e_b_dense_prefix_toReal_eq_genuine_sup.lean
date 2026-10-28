-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_dense_prefix_toReal_eq_genuine_sup
-- name    : AvramDividend.Classical.avram_ws01e_b_dense_prefix_toReal_eq_genuine_sup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T17:34:57.79075+00:00
-- url     : https://prove2.me/theorems/4d43b293-d437-4db7-b345-f42ff2ceb384
-- title:
--   Dense sampled clipped ENNReal prefix supremum equals the genuine real finite-horizon path supremum at sampled endpoint
-- statement:
--   For any right-continuous real path on nonnegative time starting from zero, and any countable dense sampling schedule containing zero and the terminal time t, the real value of the ENNReal countable supremum of clipped sampled path levels at times at most t is exactly the actual supremum over the whole interval [0,t], provided the latter is bounded above. This repairs the essential pathwise gap between the fully Pi-measurable dyadic prefix reward 46658681 and the genuine running supremum in finite-rate Esscher Wiener–Hopf record regeneration 4cf7269f. The endpoint condition is needed for a cadlag terminal upward record; f(0)=0 ensures the clipped observations do not affect a nonnegative running supremum.
-- source:
--   Proved dense_timeSup_with_endpoint 4cdf4ed6-71c6-4948-849b-8bfefa587f36, canonical Mathlib ENNReal.toReal_iSup and true finite-rate tilted upper-record regeneration 4cf7269f-2479-43da-9d75-ab22ce6f7c26.

import Mathlib
open MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_dense_prefix_toReal_eq_genuine_sup
    (f : ℝ≥0 → ℝ) (hr : ∀ u, ContinuousWithinAt f (Set.Ici u) u)
    (hfzero : f 0 = 0)
    (samples : ℕ → ℝ≥0)
    (hdense : Dense (Set.range samples))
    (hzero : (0 : ℝ≥0) ∈ Set.range samples)
    (t : ℝ≥0) (ht : t ∈ Set.range samples)
    (hb : BddAbove (Set.range (fun s : Set.Icc (0 : ℝ≥0) t => f s.1))) :
    (⨆ i : ℕ, if samples i ≤ t then
      ENNReal.ofReal (f (samples i)) else 0).toReal =
      ⨆ s : Set.Icc (0 : ℝ≥0) t, f s.1 := by sorry
