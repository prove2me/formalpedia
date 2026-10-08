-- Prove2me | Theorems.Thm_BookProof_FockNumberPreservingGap_isPosCol_shiftCol_diagCol
-- name    : BookProof.FockNumberPreservingGap.isPosCol_shiftCol_diagCol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T20:44:58.678051+00:00
-- url     : https://prove2.me/theorems/8bceaf0a-31b9-49ff-8c97-10b5b4dd1c90
-- title:
--   `BookProof.FockNumberPreservingGap.isPosCol_shiftCol_diagCol` {e : ℕ → ℝ} {mu : ℝ} (he : ∀ k, mu ≤ e k) : IsPosCol (shiftCol (diagCol e) mu)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockNumberPreservingGap`.
--
--   `BookProof.FockNumberPreservingGap.isPosCol_shiftCol_diagCol` {e : ℕ → ℝ} {mu : ℝ} (he : ∀ k, mu ≤ e k) : IsPosCol (shiftCol (diagCol e) mu)
--
--   Formalization note: Lean 4 identifier `BookProof.FockNumberPreservingGap.isPosCol_shiftCol_diagCol`.

-- Generated from ChapterFockNumberPreservingGap.lean — theorem BookProof.FockNumberPreservingGap.isPosCol_shiftCol_diagCol
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.FockNumberPreservingGap


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

theorem BookProof.FockNumberPreservingGap.isPosCol_shiftCol_diagCol {e : ℕ → ℝ} {mu : ℝ} (he : ∀ k, mu ≤ e k) :
    IsPosCol (shiftCol (diagCol e) mu) := by sorry
