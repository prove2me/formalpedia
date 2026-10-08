-- Prove2me | Theorems.Thm_BookProof_FockNumberPreservingGap_creVec_sub
-- name    : BookProof.FockNumberPreservingGap.creVec_sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T20:27:14.006515+00:00
-- url     : https://prove2.me/theorems/369ca94b-9526-439e-a826-4ab588d1f27b
-- title:
--   `BookProof.FockNumberPreservingGap.creVec_sub` (v w : ℕ →₀ ℂ) (x : FockAlg) : creVec (v - w) x = creVec v x - creVec w x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockNumberPreservingGap`.
--
--   `BookProof.FockNumberPreservingGap.creVec_sub` (v w : ℕ →₀ ℂ) (x : FockAlg) : creVec (v - w) x = creVec v x - creVec w x
--
--   Formalization note: Lean 4 identifier `BookProof.FockNumberPreservingGap.creVec_sub`.

-- Generated from ChapterFockNumberPreservingGap.lean — theorem BookProof.FockNumberPreservingGap.creVec_sub
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization
open BookProof.FockNumberPreservingGap


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

theorem BookProof.FockNumberPreservingGap.creVec_sub (v w : ℕ →₀ ℂ) (x : FockAlg) :
    creVec (v - w) x = creVec v x - creVec w x := by sorry
