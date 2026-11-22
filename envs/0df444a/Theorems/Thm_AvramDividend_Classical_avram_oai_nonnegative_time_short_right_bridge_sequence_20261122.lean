-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_nonnegative_time_short_right_bridge_sequence_20261122
-- name    : AvramDividend.Classical.avram_oai_nonnegative_time_short_right_bridge_sequence_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:32:13.995106+00:00
-- url     : https://prove2.me/theorems/89b83715-b9b1-4b27-b1a6-a193f4870f6e
-- title:
--   Canonical strictly positive, bounded right-time approximants s<r_k≤t approaching s and preserving remaining interval length
-- statement:
--   For any two nonnegative times s<t, produce an explicit deterministic interior right-time sequence r_k = s+(t-s)/(k+1), satisfying s<r_k≤t, r_k−s→0 and t−r_k→t−s. This discharges the technical short-time right-continuity collar hypothesis in the already Proved real finite Borel mark conditional centring source theorem, enabling actual physical negative simple-mark compensated increments to have right-continuous-past conditional zero for every s<t, with no artificially supplied sequence.

import Mathlib
open Filter
open scoped NNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_nonnegative_time_short_right_bridge_sequence_20261122
    (s t : ℝ≥0) (hst : s < t) :
    ∃ r : ℕ → ℝ≥0,
      (∀ k, s < r k) ∧
      (∀ k, r k ≤ t) ∧
      Tendsto (fun k => r k - s) atTop (𝓝 0) ∧
      Tendsto (fun k => t - r k) atTop (𝓝 (t - s)) := by sorry
