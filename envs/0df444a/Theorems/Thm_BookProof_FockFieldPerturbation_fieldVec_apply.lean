-- Prove2me | Theorems.Thm_BookProof_FockFieldPerturbation_fieldVec_apply
-- name    : BookProof.FockFieldPerturbation.fieldVec_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:20:59.609255+00:00
-- url     : https://prove2.me/theorems/b0eeda8d-6197-4b67-9b47-fe478d803d22
-- title:
--   `BookProof.FockFieldPerturbation.fieldVec_apply` (f : ℕ →₀ ℂ) (x : FockAlg) : fieldVec f x = creVec f x + annVec f x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockFieldPerturbation`.
--
--   `BookProof.FockFieldPerturbation.fieldVec_apply` (f : ℕ →₀ ℂ) (x : FockAlg) : fieldVec f x = creVec f x + annVec f x
--
--   Formalization note: Lean 4 identifier `BookProof.FockFieldPerturbation.fieldVec_apply`.

-- Generated from ChapterFockFieldPerturbation.lean — theorem BookProof.FockFieldPerturbation.fieldVec_apply
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

theorem BookProof.FockFieldPerturbation.fieldVec_apply (f : ℕ →₀ ℂ) (x : FockAlg) :
    fieldVec f x = creVec f x + annVec f x := by sorry
