-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_piecewisePath_increment_band
-- name    : AvramDividend.Classical.avram_a06_piecewisePath_increment_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:26:57.681063+00:00
-- url     : https://prove2.me/theorems/51e49fac-5e28-4841-9ffc-00d0129d31b4
-- title:
--   Original compound-Poisson piecewise path increment equals drift plus arrival-band marks
-- statement:
--   A finite-variation compound-Poisson path increment is the drift contribution plus the exact sum of arrival-band marks. This deterministic identity is needed to transfer original marked-renewal band independence and stationarity to the compound-Poisson increments, retaining the same original process and sample space.
-- source:
--   Original LeanLevy piecewisePath definition and pinned Finset.sum_Ico_eq_sub identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_piecewisePath
import Definitions.Def_levy_foundations_jumpCount
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_piecewisePath_increment_band
    (b : ℝ) (T Y : ℕ → ℝ) (s t : ℝ)
    (hcount : LevyFoundations.jumpCount T s ≤ LevyFoundations.jumpCount T t) :
    LevyFoundations.piecewisePath 0 b T Y t -
        LevyFoundations.piecewisePath 0 b T Y s =
      b * (t - s) +
        ∑ n ∈ Finset.Ico (LevyFoundations.jumpCount T s)
          (LevyFoundations.jumpCount T t), Y n := by sorry
