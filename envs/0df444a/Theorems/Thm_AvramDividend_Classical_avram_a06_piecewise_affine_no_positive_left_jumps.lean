-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_piecewise_affine_no_positive_left_jumps
-- name    : AvramDividend.Classical.avram_a06_piecewise_affine_no_positive_left_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T23:01:00.250209+00:00
-- url     : https://prove2.me/theorems/26b27850-d61d-4e97-acaa-f9975dc81e86
-- title:
--   Piecewise affine path with locally finite times and nonpositive marks has no upward left jumps
-- statement:
--   Deterministic lemma: strictly increasing diverging jump times and nonpositive marks ensure a piecewise-affine path has no strictly upward discontinuity at any positive time. On the interval immediately preceding a time, its jump count is fixed; at the time an additional jump may occur, but that jump contributes a nonpositive mark. This provides the original compound-Poisson almost-sure downward-jump event.
-- source:
--   A06 original CP negative jump certificate 4bdbe705 and good path event 9a1ae714.

import Mathlib
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_piecewisePath
open MeasureTheory Set ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a06_piecewise_affine_no_positive_left_jumps
    (x₀ b : ℝ) (T Y : ℕ → ℝ)
    (hmono : StrictMono T) (htop : Tendsto T atTop atTop)
    (hneg : ∀ n, Y n ≤ 0) :
    ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Tendsto (fun s : ℝ≥0 =>
        LevyFoundations.piecewisePath x₀ b T Y (s : ℝ))
        (nhdsWithin t (Iio t)) (nhds l) →
      LevyFoundations.piecewisePath x₀ b T Y (t : ℝ) ≤ l := by sorry
