-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_prescribed_uniform_physical_grid_is_monotone_and_has_exact_last_clock
-- name    : AvramDividend.Classical.avram_bva_a22_original_prescribed_uniform_physical_grid_is_monotone_and_has_exact_last_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:28:21.975741+00:00
-- url     : https://prove2.me/theorems/4d0528b8-b0e7-4f8e-8c51-181d49f8cbf6
-- title:
--   Supplied original positive-horizon uniform physical clocks are monotone and attain exactly T minus one mesh width at the last observed index
-- statement:
--   For the original classical spectrally negative Levy stopped verification proof, the physical clock u(n,i) is prescribed, not selected adaptively. Given positive physical horizon T, time zero u(n,0)=0 and literal uniform clock equality u(n,i)=T*i/(n+2) in nonnegative reals, prove both physical-grid assumptions used by the HJB signed budget: exact last left endpoint u(n,n+1)=T-T/(n+2), and monotonicity u(n,i)<=u(n,i+1) for every row and cell. The result permits direct reuse of the proved original physical HJB expectation theorem on the same prescribed source BVA-A22 physical clock. No grid reindexing, faster spatial band rate or altered physical or stochastic source is introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_prescribed_uniform_physical_grid_is_monotone_and_has_exact_last_clock
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hu0 : ∀ n, u n 0 = 0)
    (huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2)) :
    (∀ n, u n 0 = 0 ∧
      (u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)) ∧
    (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) := by sorry
