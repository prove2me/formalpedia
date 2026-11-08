-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_large_reserve_integrand_zero
-- name    : AvramDividend.Classical.avram_a19_affine_singular_large_reserve_integrand_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:40:44.134459+00:00
-- url     : https://prove2.me/theorems/640330e6-91f8-4fb9-ab4e-cfcbc42004f0
-- title:
--   Original compensated singular jump integrand vanishes above reserve one
-- statement:
--   At every reserve at least one, the compensated generator integrand of the zero-extended affine value candidate is zero for each jump in the singular Levy measure's negative support.
-- source:
--   A19 original generator countermodel global positive-reserve HJB interface, relying on the companion derivative-one theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_zero_extension_deriv_one
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a19_affine_singular_large_reserve_integrand_zero
    (x z : ℝ) (hx : 1 ≤ x) (hz : z ∈ Ioo (-1 : ℝ) 0) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x z = 0 := by sorry
