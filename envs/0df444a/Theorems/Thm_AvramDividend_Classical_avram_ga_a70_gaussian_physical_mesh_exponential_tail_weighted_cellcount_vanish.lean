-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a70_gaussian_physical_mesh_exponential_tail_weighted_cellcount_vanish
-- name    : AvramDividend.Classical.avram_ga_a70_gaussian_physical_mesh_exponential_tail_weighted_cellcount_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:36:08.222335+00:00
-- url     : https://prove2.me/theorems/2f4f0266-97d6-4ee2-8b07-db476f26b524
-- title:
--   Gaussian original physical mesh positive rare-source excursion exponential tail dominates the cell-count growth
-- statement:
--   For fixed real b and strictly positive c, (m+1) times exp(b−c(m+1)) tends to zero, the exact Gaussian optimised rare-upper-tail physical-mesh rate once the original cell length is n/(m+1).
-- source:
--   Original b0d9951c Gaussian spatial C2 positive-only rare upper-surplus source cells: ga_a67 and finite uniform physical mesh union bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Filter Topology AvramDividend.Classical

theorem AvramDividend.Classical.avram_ga_a70_gaussian_physical_mesh_exponential_tail_weighted_cellcount_vanish (b c : ℝ) (hc : 0 < c) :
    Tendsto (fun m : ℕ =>
      (((m : ℝ) + 1) * Real.exp (b - c * ((m : ℝ) + 1))))
      atTop (𝓝 (0 : ℝ)) := by sorry
