-- Prove2me | Theorems.Thm_BookProof_FockFieldPerturbation_fieldVec_relative_form_bound
-- name    : BookProof.FockFieldPerturbation.fieldVec_relative_form_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:35:55.040452+00:00
-- url     : https://prove2.me/theorems/06ee840b-e182-4879-a93f-c8dc483635ed
-- title:
--   `BookProof.FockFieldPerturbation.fieldVec_relative_form_bound` {col : ℕ → (ℕ →₀ ℂ)} {mu t : ℝ} (hmu : 0 < mu) (ht : 0 < t) (hgap : IsPosCol (shiftCol col mu)) (f : ℕ →₀ ℂ)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockFieldPerturbation`.
--
--   `BookProof.FockFieldPerturbation.fieldVec_relative_form_bound` {col : ℕ → (ℕ →₀ ℂ)} {mu t : ℝ} (hmu : 0 < mu) (ht : 0 < t) (hgap : IsPosCol (shiftCol col mu)) (f : ℕ →₀ ℂ) (u : FockAlg) : |(inner ℂ (toLp u) (toLp (fieldVec f u)) : ℂ).re| ≤ t / mu * (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re + l2norm f ^ 2 / t * ‖toLp u‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.FockFieldPerturbation.fieldVec_relative_form_bound`.

-- Generated from ChapterFockFieldPerturbation.lean — theorem BookProof.FockFieldPerturbation.fieldVec_relative_form_bound
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

theorem BookProof.FockFieldPerturbation.fieldVec_relative_form_bound {col : ℕ → (ℕ →₀ ℂ)} {mu t : ℝ} (hmu : 0 < mu)
    (ht : 0 < t) (hgap : IsPosCol (shiftCol col mu)) (f : ℕ →₀ ℂ) (u : FockAlg) :
    |(inner ℂ (toLp u) (toLp (fieldVec f u)) : ℂ).re|
      ≤ t / mu * (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re
        + l2norm f ^ 2 / t * ‖toLp u‖ ^ 2 := by sorry
