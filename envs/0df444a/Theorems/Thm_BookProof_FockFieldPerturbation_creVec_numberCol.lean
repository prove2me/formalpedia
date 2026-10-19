-- Prove2me | Theorems.Thm_BookProof_FockFieldPerturbation_creVec_numberCol
-- name    : BookProof.FockFieldPerturbation.creVec_numberCol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:21:11.644314+00:00
-- url     : https://prove2.me/theorems/6c07a461-6390-4220-a68f-686c752e9c35
-- title:
--   `BookProof.FockFieldPerturbation.creVec_numberCol` (k : ℕ) (x : FockAlg) : creVec (numberCol k) x = creA k x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockFieldPerturbation`.
--
--   `BookProof.FockFieldPerturbation.creVec_numberCol` (k : ℕ) (x : FockAlg) : creVec (numberCol k) x = creA k x
--
--   Formalization note: Lean 4 identifier `BookProof.FockFieldPerturbation.creVec_numberCol`.

-- Generated from ChapterFockFieldPerturbation.lean — theorem BookProof.FockFieldPerturbation.creVec_numberCol
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Mathlib
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.FockFieldPerturbation


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability

theorem BookProof.FockFieldPerturbation.creVec_numberCol (k : ℕ) (x : FockAlg) : creVec (numberCol k) x = creA k x := by sorry
