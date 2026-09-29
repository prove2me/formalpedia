-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_creA_annA_single
-- name    : BookProof.FockOneParticleGap.creA_annA_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:09:10.905698+00:00
-- url     : https://prove2.me/theorems/0ce50622-0c5a-4d1a-ab27-5dcc91b4a0d2
-- title:
--   (k : ℕ) (β : Conf) (c : ℂ) : creA k (annA k (Finsupp.single β c)) = ((β k : ℝ) : ℂ) • Finsupp.single β c
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.creA_annA_single` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.creA_annA_single
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

theorem BookProof.FockOneParticleGap.creA_annA_single (k : ℕ) (β : Conf) (c : ℂ) :
    creA k (annA k (Finsupp.single β c)) = ((β k : ℝ) : ℂ) • Finsupp.single β c := by sorry
