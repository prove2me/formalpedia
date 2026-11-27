-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_compact_secant
-- name    : AvramDividend.Classical.avram_locmoll_band_compact_secant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:24:51.656333+00:00
-- url     : https://prove2.me/theorems/2ba9377c-61d0-5bdb-9302-8561576fb120
-- title:
--   Globally smooth value has a finite Lipschitz constant on the compact reserve interval
-- statement:
--   Globally smooth value has a finite Lipschitz constant on the compact reserve interval
-- source:
--   Exact dividend convergence reduction of 5d5b4160-dbec-53b8-b2ad-8979f199b2d3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_compact_secant
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a ∈ Icc 0 R, ∀ b ∈ Icc 0 R,
      |g a - g b| ≤ K * |a - b| := by sorry
