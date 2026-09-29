-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_conj_mul_re
-- name    : BookProof.FockOneParticleGap.conj_mul_re
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:37:21.060287+00:00
-- url     : https://prove2.me/theorems/6c81df05-235f-4b62-88b3-7c1eb788773d
-- title:
--   (z : ℂ) : ((starRingEnd ℂ) z * z).re = ‖z‖ ^ 2
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.conj_mul_re` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.conj_mul_re
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

theorem BookProof.FockOneParticleGap.conj_mul_re (z : ℂ) : ((starRingEnd ℂ) z * z).re = ‖z‖ ^ 2 := by sorry
