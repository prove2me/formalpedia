-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_secant_cell_mass
-- name    : AvramDividend.Classical.avram_locmoll_band_secant_cell_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:40:33.878661+00:00
-- url     : https://prove2.me/theorems/479cf526-19d1-442d-8471-4b4e21f4d653
-- title:
--   Extended secant multiplied by its cell mass gives the exact value difference
-- statement:
--   Extended secant multiplied by its cell mass gives the exact value difference
-- source:
--   Physical Stieltjes integral route to 8b646752-f25d-4029-9771-dda1d287c7e1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_secant_cell_mass
    (g : ℝ → ℝ) (a b : ℝ) :
    let Q : ℝ → ℝ → ℝ := fun a b => if a = b then deriv g a else (g a - g b) / (a - b)
    Q a b * (a - b) = g a - g b := by sorry
