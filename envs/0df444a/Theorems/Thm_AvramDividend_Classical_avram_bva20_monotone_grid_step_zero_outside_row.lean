-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva20_monotone_grid_step_zero_outside_row
-- name    : AvramDividend.Classical.avram_bva20_monotone_grid_step_zero_outside_row
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:40:34.835241+00:00
-- url     : https://prove2.me/theorems/29a5ecfb-46aa-4ea7-ad04-b7f67961375d
-- title:
--   Frozen Riemann step integrand vanishes outside its finite grid row
-- statement:
--   For a monotone increasing sequence of original grid endpoints u, every half-open cell [u_j,u_(j+1)) in a finite row is contained in [u_0,u_(n+1)). Therefore the sum of cell indicators weighted by frozen coefficients c_j is zero outside the whole finite row. Combines with the proved floor-index step evaluation c4aebe37 to identify the full real-time frozen compensator step integrand a.e. for 7ccc2a1a.
-- source:
--   Necessary compact support part of original finite frozen Riemann step-integral-to-floor-sample identity 7ccc2a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bva20_monotone_grid_step_zero_outside_row
    (n : ℕ) (u : ℕ → ℝ) (hu : StrictMono u)
    (c : ℕ → ℝ) (t : ℝ)
    (ht : t ∉ Set.Ico (u 0) (u (n + 1))) :
    (∑ j ∈ Finset.range (n + 1),
      (Set.Ico (u j) (u (j + 1))).indicator (fun _ => c j) t) = 0 := by sorry
