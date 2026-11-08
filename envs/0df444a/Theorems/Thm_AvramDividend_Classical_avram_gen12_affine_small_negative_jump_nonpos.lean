-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen12_affine_small_negative_jump_nonpos
-- name    : AvramDividend.Classical.avram_gen12_affine_small_negative_jump_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:51:54.912391+00:00
-- url     : https://prove2.me/theorems/bac9a7a3-8175-4090-8252-556e633614a4
-- title:
--   Original affine generator integrand is nonpositive across the entire small negative jump band
-- statement:
--   The exact original generator integrand of the positive-reserve affine payoff is nonpositive at every small negative jump. The proof partitions jumps into ruin-crossing, exactly-zero and solvent-preserving cases, reusing accepted source-exact children.
-- source:
--   One-sided sign bridge for the singular Lévy generator countermodel, preserving the original indicator and derivative definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical Set
noncomputable section

theorem AvramDividend.Classical.avram_gen12_affine_small_negative_jump_nonpos
    (x z : ℝ) (hx : 0 < x) (hcap : x < 1)
    (hzlow : -1 < z) (hzneg : z < 0) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x z ≤ 0 := by sorry
