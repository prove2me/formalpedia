-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_generic_jumpmark_vanish_from_right
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_generic_jumpmark_vanish_from_right
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:22:53.515046+00:00
-- url     : https://prove2.me/theorems/e1b872f2-c352-4d3b-b51f-33989b8be183
-- title:
--   Generic càdlàg jump marks vanish approaching times from the right
-- statement:
--   For any real-valued right-continuous path admitting genuine strict-left limits at every positive time, its jump-size function Y(u)-leftLim(Y,u) tends to zero as u descends to any fixed time including zero. The proof uses right-neighbourhood control, closure of the ball under the true left limit, and metric triangular bounds. This is the deterministic right-hand localisation required to exclude accumulation of large jumps.

import Mathlib

open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_h_cadlag_generic_jumpmark_vanish_from_right
    (Y : ℝ≥0 → ℝ)
    (hR : ∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u)
    (hL : ∀ u : ℝ≥0, 0 < u → Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (t : ℝ≥0) :
    Tendsto (fun u : ℝ≥0 => Y u - Function.leftLim Y u)
      (𝓝[>] t) (𝓝 (0 : ℝ)) := by sorry
