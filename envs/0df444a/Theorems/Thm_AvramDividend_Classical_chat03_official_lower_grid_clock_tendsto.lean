-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_official_lower_grid_clock_tendsto
-- name    : AvramDividend.Classical.chat03_official_lower_grid_clock_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T06:53:35.598724+00:00
-- url     : https://prove2.me/theorems/98e1e0fc-6654-4b06-a515-effcb63e0e87
-- title:
--   Exact official strict lower uniform-grid first-passage clock converges, including infinity
-- statement:
--   For any official spectrally negative Lévy sample path, strict lower first-passage times sampled on positive uniform grids with mesh tending to zero converge in ENNReal to the named continuous strict lower passage time. If the continuous passage is infinite, every grid clock is infinite. For a finite continuous passage, its ENNReal infimum gives an NNReal greatest lower bound, and the accepted strict lower mesh bracket plus the accepted ENNReal convergence-from-eventual-brackets theorem yield convergence. Grid crossing sets may be empty at coarse mesh sizes.
-- source:
--   Accepted Chat 03 exact lower ENNReal grid bracket, finite first-passage infimum bridge, general ENNReal convergence bridge and infinite lower no-exit persistence at pinned Mathlib.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_finite_extended_infimum_isGLB
import Theorems.Thm_AvramDividend_Classical_chat03_lower_grid_ennreal_bracket
import Theorems.Thm_AvramDividend_Classical_chat03_ennreal_grid_clock_tendsto_of_mesh_brackets
import Theorems.Thm_AvramDividend_Classical_chat03_official_no_lower_exit_grid_inf_top

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat03_official_lower_grid_clock_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower : ℝ)
    (mesh : ℕ → ℝ≥0)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0))) :
    Tendsto
      (fun n => ⨅ k : ℕ,
        if X.X ((k : ℝ≥0) * mesh n) ω < lower then
          (((k : ℝ≥0) * mesh n) : ℝ≥0∞)
        else ∞)
      atTop (𝓝 (twoSidedExitDownTime X lower ω)) := by sorry
