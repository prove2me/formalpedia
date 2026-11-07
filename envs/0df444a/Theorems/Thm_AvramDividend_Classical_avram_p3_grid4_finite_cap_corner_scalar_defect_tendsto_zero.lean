-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_corner_scalar_defect_tendsto_zero
-- name    : AvramDividend.Classical.avram_p3_grid4_finite_cap_corner_scalar_defect_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:50:48.105363+00:00
-- url     : https://prove2.me/theorems/e9769c10-33a8-4796-86ca-0e9bb9603244
-- title:
--   Finite-cap slope-one cutoff secant defect vanishes by continuity without any boundary derivative
-- statement:
--   For any positive finite real cap c and any continuous original HJB candidate w on the nonnegative halfline, along any deterministic interior cutoff sequence b_n→c the scalar secant defect [w(c)-w(b_n)]-[c-b_n] tends to zero. No smooth-fit derivative at c is assumed. Combined with a uniform cap-linear C1 cutoff estimate, this supplies zero cap-corner approximation error on all original reserve paths, avoiding the unsupported endpoint-slope assumption in earlier mesh-error adapters.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_finite_cap_corner_scalar_defect_tendsto_zero
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_cont : ContinuousOn w (Ici 0))
    (b : ℕ → ℝ) (hb : Tendsto b atTop (𝓝 c)) :
    Tendsto (fun n => (w c - w (b n)) - (c - b n))
      atTop (𝓝 (0 : ℝ)) := by sorry
