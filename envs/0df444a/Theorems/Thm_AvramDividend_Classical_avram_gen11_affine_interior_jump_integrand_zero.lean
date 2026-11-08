-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen11_affine_interior_jump_integrand_zero
-- name    : AvramDividend.Classical.avram_gen11_affine_interior_jump_integrand_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:39:17.284307+00:00
-- url     : https://prove2.me/theorems/2682a7f7-d806-4b23-8423-8c0487d12276
-- title:
--   Original affine generator remainder vanishes for small solvent-preserving negative jumps
-- statement:
--   For a positive reserve below the cap one, a small negative jump that leaves reserve strictly positive has no affine payoff Taylor remainder. Thus the source generator jump term vanishes inside solvency, with all nonzero singular contribution concentrated at ruin-crossing jumps.
-- source:
--   Complementary source-exact original generator child for the A19 boundary-singular countermodel. Uses the derivative-one positive-reserve theorem in its candidate proof; the formal statement remains independent.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical Set
noncomputable section

theorem AvramDividend.Classical.avram_gen11_affine_interior_jump_integrand_zero
    (x z : ℝ) (hx : 0 < x) (hcap : x < 1)
    (hzin : -x < z) (hzneg : z < 0) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x z = 0 := by sorry
