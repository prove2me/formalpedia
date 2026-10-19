-- Prove2me | Theorems.Thm_BookProof_FockFieldPerturbation_annVec_apply
-- name    : BookProof.FockFieldPerturbation.annVec_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:20:35.904328+00:00
-- url     : https://prove2.me/theorems/33cebde2-0887-4182-aaa2-2f84e4b99c99
-- title:
--   `BookProof.FockFieldPerturbation.annVec_apply` (f : ℕ →₀ ℂ) (x : FockAlg) : annVec f x = ∑ j ∈ f.support, ((starRingEnd ℂ) (f j)) • annA j x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockFieldPerturbation`.
--
--   `BookProof.FockFieldPerturbation.annVec_apply` (f : ℕ →₀ ℂ) (x : FockAlg) : annVec f x = ∑ j ∈ f.support, ((starRingEnd ℂ) (f j)) • annA j x
--
--   Formalization note: Lean 4 identifier `BookProof.FockFieldPerturbation.annVec_apply`.

-- Generated from ChapterFockFieldPerturbation.lean — theorem BookProof.FockFieldPerturbation.annVec_apply
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

theorem BookProof.FockFieldPerturbation.annVec_apply (f : ℕ →₀ ℂ) (x : FockAlg) :
    annVec f x = ∑ j ∈ f.support, ((starRingEnd ℂ) (f j)) • annA j x := by sorry
