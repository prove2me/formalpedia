-- Prove2me | Theorems.Thm_BookProof_FockNumberPreservingGap_shiftCol_diagCol
-- name    : BookProof.FockNumberPreservingGap.shiftCol_diagCol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T20:26:28.636656+00:00
-- url     : https://prove2.me/theorems/a27685be-8753-45c5-ac31-0586ae91c4f7
-- title:
--   `BookProof.FockNumberPreservingGap.shiftCol_diagCol` (e : ℕ → ℝ) (mu : ℝ) : shiftCol (diagCol e) mu = diagCol fun k => e k - mu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockNumberPreservingGap`.
--
--   `BookProof.FockNumberPreservingGap.shiftCol_diagCol` (e : ℕ → ℝ) (mu : ℝ) : shiftCol (diagCol e) mu = diagCol fun k => e k - mu
--
--   Formalization note: Lean 4 identifier `BookProof.FockNumberPreservingGap.shiftCol_diagCol`.

-- Generated from ChapterFockNumberPreservingGap.lean — theorem BookProof.FockNumberPreservingGap.shiftCol_diagCol
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

theorem BookProof.FockNumberPreservingGap.shiftCol_diagCol (e : ℕ → ℝ) (mu : ℝ) :
    shiftCol (diagCol e) mu = diagCol fun k => e k - mu := by sorry
