-- Prove2me | Theorems.Thm_BookProof_FockNumberPreservingGap_shiftCol_opCol
-- name    : BookProof.FockNumberPreservingGap.shiftCol_opCol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T20:45:49.427809+00:00
-- url     : https://prove2.me/theorems/29ff5d35-f1ac-4f7f-b8ac-b9be97dc4060
-- title:
--   `BookProof.FockNumberPreservingGap.shiftCol_opCol` (b : HilbertBasis ℕ ℂ F) (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b) (mu : ℝ) : shiftCol (opCol b A) mu = opCol b (A - ((mu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockNumberPreservingGap`.
--
--   `BookProof.FockNumberPreservingGap.shiftCol_opCol` (b : HilbertBasis ℕ ℂ F) (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b) (mu : ℝ) : shiftCol (opCol b A) mu = opCol b (A - ((mu : ℝ) : ℂ) • LinearMap.id)
--
--   Formalization note: Lean 4 identifier `BookProof.FockNumberPreservingGap.shiftCol_opCol`.

-- Generated from ChapterFockNumberPreservingGap.lean — theorem BookProof.FockNumberPreservingGap.shiftCol_opCol
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

theorem BookProof.FockNumberPreservingGap.shiftCol_opCol (b : HilbertBasis ℕ ℂ F)
    (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b) (mu : ℝ) :
    shiftCol (opCol b A) mu = opCol b (A - ((mu : ℝ) : ℂ) • LinearMap.id) := by sorry
