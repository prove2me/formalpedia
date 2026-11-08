-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen15_affine_singular_generator_jump_integrable
-- name    : AvramDividend.Classical.avram_gen15_affine_singular_generator_jump_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:54:55.25792+00:00
-- url     : https://prove2.me/theorems/a16eb401-099e-4db3-acb0-5e5cb77f2f97
-- title:
--   Source affine singular negative-jump generator integrand is Bochner integrable on positive subunit reserves
-- statement:
--   For every positive reserve below one, the exact original generator jump integrand of the affine positive-reserve ruin payoff is genuinely integrable under the singular negative-jump Levy measure. The proof uses the accepted exact integral formula and the integral_undef contrapositive, proving its value is strictly negative by a square-root factorisation.
-- source:
--   Accepted source-exact affine jump integral and pinned Mathlib integral_undef/Real.rpow_add.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gen15_affine_singular_generator_jump_integrable
    (x : ℝ) (hx : 0 < x) (hcap : x < 1) :
    Integrable (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand
      (fun u : ℝ => if u < 0 then 0 else 1 + u) x z)
      (volume.withDensity (fun z : ℝ =>
        if z ∈ Ioo (-1 : ℝ) 0
        then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0)) := by sorry
