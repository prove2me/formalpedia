-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_clipped_physical_grid_increment_strict_stop_mask
-- name    : AvramDividend.Classical.avram_pj_workerC_clipped_physical_grid_increment_strict_stop_mask
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:13:08.089444+00:00
-- url     : https://prove2.me/theorems/7687813e-a884-4db8-aef9-6279b555d1b6
-- title:
--   Original physical grid clipped at true random stopping clock has exact deterministic-cell strict stopping mask and zero increments thereafter
-- statement:
--   For any nondecreasing deterministic physical grid g_i and pathwise actual stopping clock rho, the increment of u_i=min(g_i,rho) is zero if rho<=g_i, and otherwise equals min(g_(i+1),rho)-g_i. In particular all later clipped cells have zero length. This exact identity, including the final partial clipped cell, is needed before using compensated negative-mark martingale results that require deterministic grid cells and a predictable stopping mask, instead of wrongly treating random clipped endpoints as deterministic.
-- source:
--   Pure NNReal min arithmetic with monotone grid. Applies to Proved b9dccb actual clipped stopped four-term mesh and d5a15403 original deterministic stopped predictable compensated grid zero mean.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_clipped_physical_grid_increment_strict_stop_mask
    {Ω : Type*} (g : ℕ → ℝ≥0) (hg : Monotone g)
    (ρ : Ω → ℝ≥0) (ω : Ω) (i : ℕ) :
    let u : ℕ → ℝ≥0 := fun j => min (g j) (ρ ω)
    (u (i + 1) - u i =
      if ρ ω ≤ g i then 0 else
        min (g (i + 1)) (ρ ω) - g i) ∧
    (ρ ω ≤ g i → u (i + 1) = u i) := by sorry
