-- Prove2me | solution 1 for mme_matMulExp_strassen_pos
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-30T19:10:33.740576+00:00
-- url     : https://prove2.me/submissions/1d3852ff-dd0d-4311-abe4-6630c4428a2d

import Definitions.Def_mme_omega_pos

/-! # Solution: positivity of `matMulExp_strassen K`.

Thin re-export of `MME.matMulExp_strassen_pos` from `Def_mme_omega_pos`. -/

open MME

universe u

theorem solution {K : Type u} [Field K] : 0 < matMulExp_strassen K :=
  MME.matMulExp_strassen_pos
