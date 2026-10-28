-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_dense_timeInf_with_endpoint
-- name    : AvramDividend.Classical.avram_ws01e_b_support_dense_timeInf_with_endpoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:30:52.70584+00:00
-- url     : https://prove2.me/theorems/11740f6f-6fd3-4d55-a25e-766d7515aa46
-- title:
--   Continuous-time path infimum from dense observations with terminal endpoint
-- statement:
--   For any right-continuous real path on nonnegative time whose values on a finite closed interval are bounded below, and any dense subset of nonnegative times containing zero, the infimum over the full closed interval is the minimum of the dense-sample infimum up to that horizon and the value at the horizon itself. A possible endpoint jump is retained exactly. This provides a deterministic lower-envelope bridge for passing finite-mesh Lévy minimum and drawdown reversal identities to continuous time. No independent increments, Esscher change of law, or Wiener–Hopf independence is assumed.

import Mathlib

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_support_dense_timeInf_with_endpoint (f : ℝ≥0 → ℝ)
    (hr : ∀ u, ContinuousWithinAt f (Ici u) u)
    (S : Set ℝ≥0) (hS : Dense S) (h0 : (0 : ℝ≥0) ∈ S)
    (t : ℝ≥0)
    (hb : BddBelow (Set.range
      (fun s : Set.Icc (0 : ℝ≥0) t => f s.1))) :
    (⨅ s : Set.Icc (0 : ℝ≥0) t, f s.1) =
      min (⨅ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, f s.1) (f t) := by sorry
