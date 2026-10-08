-- Prove2me | Theorems.Thm_BookProof_FockNumberPreservingGap_creVec_smul
-- name    : BookProof.FockNumberPreservingGap.creVec_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T20:28:10.44199+00:00
-- url     : https://prove2.me/theorems/44ed6d84-ae0a-483d-bc7e-27989a7a21f0
-- title:
--   `BookProof.FockNumberPreservingGap.creVec_smul` (c : ℂ) (v : ℕ →₀ ℂ) (x : FockAlg) : creVec (c • v) x = c • creVec v x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockNumberPreservingGap`.
--
--   `BookProof.FockNumberPreservingGap.creVec_smul` (c : ℂ) (v : ℕ →₀ ℂ) (x : FockAlg) : creVec (c • v) x = c • creVec v x
--
--   Formalization note: Lean 4 identifier `BookProof.FockNumberPreservingGap.creVec_smul`.

-- Generated from ChapterFockNumberPreservingGap.lean — theorem BookProof.FockNumberPreservingGap.creVec_smul
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

theorem BookProof.FockNumberPreservingGap.creVec_smul (c : ℂ) (v : ℕ →₀ ℂ) (x : FockAlg) :
    creVec (c • v) x = c • creVec v x := by sorry
