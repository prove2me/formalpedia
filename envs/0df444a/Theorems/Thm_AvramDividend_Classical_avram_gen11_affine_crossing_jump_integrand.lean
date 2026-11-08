-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen11_affine_crossing_jump_integrand
-- name    : AvramDividend.Classical.avram_gen11_affine_crossing_jump_integrand
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:37:58.625502+00:00
-- url     : https://prove2.me/theorems/f55230db-767c-4a08-b782-42ba3d2ac398
-- title:
--   Original Lévy generator integrand at a small jump crossing ruin has a unit boundary loss
-- statement:
--   A small negative jump that crosses ruin removes the candidate payoff's unit boundary value as well as its reserve dependence. On the crossing interval the actual source generator integrand equals negative one minus the pre-jump reserve minus the jump size. This identifies the singular kernel that needs integration against the Lévy density.
-- source:
--   Source-exact generator integrand and a proven derivative child for the original A19 singular-generator countermodel. It does not assert generator integrability or evaluate the singular measure integral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical Set
noncomputable section

theorem AvramDividend.Classical.avram_gen11_affine_crossing_jump_integrand
    (x z : ℝ) (hx : 0 < x) (hzlow : -1 < z) (hzcross : z < -x) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x z =
        -1 - x - z := by sorry
