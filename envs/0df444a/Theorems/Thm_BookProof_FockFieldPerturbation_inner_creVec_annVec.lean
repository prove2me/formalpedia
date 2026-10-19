-- Prove2me | Theorems.Thm_BookProof_FockFieldPerturbation_inner_creVec_annVec
-- name    : BookProof.FockFieldPerturbation.inner_creVec_annVec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:35:29.816985+00:00
-- url     : https://prove2.me/theorems/49e4714d-c475-47fe-b377-606abea94eb7
-- title:
--   `BookProof.FockFieldPerturbation.inner_creVec_annVec` (f : ℕ →₀ ℂ) (u v : FockAlg) : (inner ℂ (toLp u) (toLp (creVec f v)) : ℂ) = inner ℂ (toLp (annVec f u)) (toLp v)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockFieldPerturbation`.
--
--   `BookProof.FockFieldPerturbation.inner_creVec_annVec` (f : ℕ →₀ ℂ) (u v : FockAlg) : (inner ℂ (toLp u) (toLp (creVec f v)) : ℂ) = inner ℂ (toLp (annVec f u)) (toLp v)
--
--   Formalization note: Lean 4 identifier `BookProof.FockFieldPerturbation.inner_creVec_annVec`.

-- Generated from ChapterFockFieldPerturbation.lean — theorem BookProof.FockFieldPerturbation.inner_creVec_annVec
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Mathlib
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization
open BookProof.FockFieldPerturbation


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability

theorem BookProof.FockFieldPerturbation.inner_creVec_annVec (f : ℕ →₀ ℂ) (u v : FockAlg) :
    (inner ℂ (toLp u) (toLp (creVec f v)) : ℂ) = inner ℂ (toLp (annVec f u)) (toLp v) := by sorry
