-- Prove2me | Theorems.Thm_BookProof_FockFieldPerturbation_abs_re_inner_fieldVec_le
-- name    : BookProof.FockFieldPerturbation.abs_re_inner_fieldVec_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:36:05.131732+00:00
-- url     : https://prove2.me/theorems/c9f51cd8-7cf6-42d4-ab8b-02dc01c99e44
-- title:
--   `BookProof.FockFieldPerturbation.abs_re_inner_fieldVec_le` (f : ℕ →₀ ℂ) (u : FockAlg) : |(inner ℂ (toLp u) (toLp (fieldVec f u)) : ℂ).re| ≤ 2 * l2norm f * Real.sqrt (numberQuad u)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockFieldPerturbation`.
--
--   `BookProof.FockFieldPerturbation.abs_re_inner_fieldVec_le` (f : ℕ →₀ ℂ) (u : FockAlg) : |(inner ℂ (toLp u) (toLp (fieldVec f u)) : ℂ).re| ≤ 2 * l2norm f * Real.sqrt (numberQuad u) * ‖toLp u‖
--
--   Formalization note: Lean 4 identifier `BookProof.FockFieldPerturbation.abs_re_inner_fieldVec_le`.

-- Generated from ChapterFockFieldPerturbation.lean — theorem BookProof.FockFieldPerturbation.abs_re_inner_fieldVec_le
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

theorem BookProof.FockFieldPerturbation.abs_re_inner_fieldVec_le (f : ℕ →₀ ℂ) (u : FockAlg) :
    |(inner ℂ (toLp u) (toLp (fieldVec f u)) : ℂ).re|
      ≤ 2 * l2norm f * Real.sqrt (numberQuad u) * ‖toLp u‖ := by sorry
