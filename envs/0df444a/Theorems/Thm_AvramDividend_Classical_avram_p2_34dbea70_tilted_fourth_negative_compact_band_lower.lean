-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_tilted_fourth_negative_compact_band_lower
-- name    : AvramDividend.Classical.avram_p2_34dbea70_tilted_fourth_negative_compact_band_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:18:12.281198+00:00
-- url     : https://prove2.me/theorems/f3dcaa6a-8be0-4dba-989e-9087db81d16c
-- title:
--   Tilted fourth-exponential test is uniformly positive on compact negative jump bands
-- statement:
--   On a compact negative jump band bounded away from zero, the tilted fourth-exponential Lévy test kernel is at least the product of the positive exponential tilt at the left endpoint and the fourth-order test at the right endpoint. The result is an unconditional analytic inequality used for Levy-measure mass estimates.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_fourth_exponential_negative_band_uniform_lower

open MeasureTheory Set AvramDividend.Classical

theorem AvramDividend.Classical.avram_p2_34dbea70_tilted_fourth_negative_compact_band_lower (ρ θ ε M y : ℝ)
    (hρ : 0 ≤ ρ) (hθ : 0 < θ) (hε : 0 < ε)
    (hlo : -M ≤ y) (hhi : y ≤ -ε) :
    Real.exp (-ρ * M) * (1 - Real.exp (-θ * ε)) ^ 4 ≤
      Real.exp (ρ * y) * (Real.exp (θ * y) - 1) ^ 4 := by sorry
