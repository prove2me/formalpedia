-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_generic_jumpmark_vanish_from_left
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_generic_jumpmark_vanish_from_left
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:22:52.310241+00:00
-- url     : https://prove2.me/theorems/4aa462be-d48e-4813-bf87-09362f56a723
-- title:
--   Generic càdlàg jump marks vanish approaching positive times from the left
-- statement:
--   For an arbitrary real-valued path with strict-left limits at each positive nonnegative-real time, its genuine jump-size function Y(u)-leftLim(Y,u) tends to zero as u approaches a positive fixed time strictly from below. This is a deterministic side-continuity lemma supporting finite ε-large jump localisation for arbitrary càdlàg paths, with no stochastic assumptions.

import Mathlib

open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_h_cadlag_generic_jumpmark_vanish_from_left
    (Y : ℝ≥0 → ℝ)
    (hL : ∀ u : ℝ≥0, 0 < u → Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (t : ℝ≥0) (ht : 0 < t) :
    Tendsto (fun u : ℝ≥0 => Y u - Function.leftLim Y u)
      (𝓝[<] t) (𝓝 (0 : ℝ)) := by sorry
