-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat05_rightCont_prefixSup_encoded_onSample
-- name    : AvramDividend.Classical.chat05_rightCont_prefixSup_encoded_onSample
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T12:25:31.229858+00:00
-- url     : https://prove2.me/theorems/56f39aec-e5e0-4454-95e6-9056e03ecbfe
-- title:
--   Right-continuous path running supremum equals sampled ENNReal record at a schedule endpoint
-- statement:
--   For a right-continuous real-valued path starting at zero, whose range over [0,t] is bounded above, the full running supremum at any time t included in a dense countable observation schedule containing zero equals the real decoding of the supremum of nonnegative ENNReal-encoded past samples. This holds also for right-continuous post-stopping-time shifted increment paths and is the pathwise bridge required in the reflected-dividend strong-Markov renewal calculation.
-- source:
--   Proved dense_timeSup_with_endpoint 4cdf4ed6 and countable_bddRealSup_eq_ennrealOfRealSup_toReal 83c83f86; generalises Proved runningSup_eq_countableENNReal_record 1f83943d to shifted right-continuous paths.

import Theorems.Thm_AvramDividend_Classical_dense_timeSup_with_endpoint
import Theorems.Thm_AvramDividend_Classical_countable_bddRealSup_eq_ennrealOfRealSup_toReal

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat05_rightCont_prefixSup_encoded_onSample
    (f : ℝ≥0 → ℝ)
    (hr : ∀ u, ContinuousWithinAt f (Ici u) u)
    (hf0 : f 0 = 0)
    (samples : ℕ → ℝ≥0)
    (hdense : Dense (Set.range samples))
    (hzero : (0 : ℝ≥0) ∈ Set.range samples)
    (t : ℝ≥0) (ht : t ∈ Set.range samples)
    (hb : BddAbove (Set.range
      (fun s : Set.Icc (0 : ℝ≥0) t => f s.1))) :
    (⨆ s : Set.Icc (0 : ℝ≥0) t, f s.1) =
      (⨆ j : ℕ, ENNReal.ofReal
        (if samples j ≤ t then max 0 (f (samples j)) else 0)).toReal := by
  sorry
