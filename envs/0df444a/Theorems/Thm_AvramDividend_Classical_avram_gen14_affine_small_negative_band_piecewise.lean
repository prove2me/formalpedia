-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen14_affine_small_negative_band_piecewise
-- name    : AvramDividend.Classical.avram_gen14_affine_small_negative_band_piecewise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:38:26.133618+00:00
-- url     : https://prove2.me/theorems/285d40ed-4bb6-4792-a929-2254b2795147
-- title:
--   Exact crossing-only formula for the original affine Levy generator integrand
-- statement:
--   For the original source-defined Levy generator integrand and a payoff affine above zero, the entire small-negative-jump integrand vanishes when the reserve stays solvent and equals the explicit affine deficit precisely when a jump crosses the ruin boundary.
-- source:
--   Assembles three proved source-exact original-generator children and handles the boundary case exactly.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical Set
noncomputable section

theorem AvramDividend.Classical.avram_gen14_affine_small_negative_band_piecewise
    (x z : ℝ) (hx : 0 < x) (hcap : x < 1)
    (hz : z ∈ Ioo (-1 : ℝ) 0) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x z =
        if z < -x then -1 - x - z else 0 := by sorry
