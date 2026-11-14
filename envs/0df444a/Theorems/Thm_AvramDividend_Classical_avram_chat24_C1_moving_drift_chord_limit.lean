-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_C1_moving_drift_chord_limit
-- name    : AvramDividend.Classical.avram_chat24_C1_moving_drift_chord_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:30:32.835333+00:00
-- url     : https://prove2.me/theorems/f58429dc-9f75-4ec1-87e0-87d3e2fa1c1b
-- title:
--   C1 moving drift chords converge to the derivative
-- statement:
--   Independent analytic prerequisite of pointwise parent a2bf4695-628f-49e6-ac17-bf0b48efe4f2. If x tends to y, mass m and mesh h tend to zero, and h is never zero, the moving chord of a C1 function between x-m and x+d*h-m, divided by h, tends to d times its derivative at y. This is a strict-derivative little-o estimate, with a saved complete research proof in /tmp/p2m-drift-moving-chord-research.lean. It assumes no grid, path regularity, jump summability, measure, or parent theorem.

import Mathlib
open MeasureTheory Set Filter Asymptotics
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_chat24_C1_moving_drift_chord_limit
    (w : ℝ → ℝ) (y d : ℝ) (x m h : ℕ → ℝ)
    (hw : ContDiffAt ℝ 1 w y)
    (hx : Tendsto x atTop (𝓝 y))
    (hm : Tendsto m atTop (𝓝 0)) (hh : Tendsto h atTop (𝓝 0))
    (hne : ∀ n, h n ≠ 0) :
    Tendsto (fun n => (w (x n + d * h n - m n) - w (x n - m n)) / h n)
      atTop (𝓝 (d * deriv w y)) := by sorry
