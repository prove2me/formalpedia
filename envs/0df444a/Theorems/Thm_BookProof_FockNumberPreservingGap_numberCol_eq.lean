-- Prove2me | Theorems.Thm_BookProof_FockNumberPreservingGap_numberCol_eq
-- name    : BookProof.FockNumberPreservingGap.numberCol_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T20:22:56.318513+00:00
-- url     : https://prove2.me/theorems/aa03a2da-d4ff-4014-bfb7-4c443c482580
-- title:
--   `BookProof.FockNumberPreservingGap.numberCol_eq` (k : ℕ) : numberCol k = Finsupp.single k (1 : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockNumberPreservingGap`.
--
--   `BookProof.FockNumberPreservingGap.numberCol_eq` (k : ℕ) : numberCol k = Finsupp.single k (1 : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.FockNumberPreservingGap.numberCol_eq`.

-- Generated from ChapterFockNumberPreservingGap.lean — theorem BookProof.FockNumberPreservingGap.numberCol_eq
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

theorem BookProof.FockNumberPreservingGap.numberCol_eq (k : ℕ) : numberCol k = Finsupp.single k (1 : ℂ) := by sorry
