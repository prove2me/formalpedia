-- Prove2me | Theorems.Thm_BookProof_FockNumberPreservingGap_opCol_id
-- name    : BookProof.FockNumberPreservingGap.opCol_id
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T20:45:43.810534+00:00
-- url     : https://prove2.me/theorems/7ee4eb8d-bb35-4721-9acf-8882dc0a0bfb
-- title:
--   `BookProof.FockNumberPreservingGap.opCol_id` (b : HilbertBasis ℕ ℂ F) (k j : ℕ) : opCol b (LinearMap.id) k j = if j = k then (1 : ℂ) else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockNumberPreservingGap`.
--
--   `BookProof.FockNumberPreservingGap.opCol_id` (b : HilbertBasis ℕ ℂ F) (k j : ℕ) : opCol b (LinearMap.id) k j = if j = k then (1 : ℂ) else 0
--
--   Formalization note: Lean 4 identifier `BookProof.FockNumberPreservingGap.opCol_id`.

-- Generated from ChapterFockNumberPreservingGap.lean — theorem BookProof.FockNumberPreservingGap.opCol_id
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.FockSecondQuantization
open BookProof.HermiteGalerkin
open BookProof.FockNumberPreservingGap

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

theorem BookProof.FockNumberPreservingGap.opCol_id (b : HilbertBasis ℕ ℂ F) (k j : ℕ) :
    opCol b (LinearMap.id) k j = if j = k then (1 : ℂ) else 0 := by sorry
