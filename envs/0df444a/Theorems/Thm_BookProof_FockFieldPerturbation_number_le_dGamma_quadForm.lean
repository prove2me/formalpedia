-- Prove2me | Theorems.Thm_BookProof_FockFieldPerturbation_number_le_dGamma_quadForm
-- name    : BookProof.FockFieldPerturbation.number_le_dGamma_quadForm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:35:46.872983+00:00
-- url     : https://prove2.me/theorems/99d5a2e3-2517-4af1-81c6-ce817563ffe1
-- title:
--   `BookProof.FockFieldPerturbation.number_le_dGamma_quadForm` {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ} (hgap : IsPosCol (shiftCol col mu)) (u : FockAlg) : mu * numberQuad u ≤ (inner ℂ (toLp u)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockFieldPerturbation`.
--
--   `BookProof.FockFieldPerturbation.number_le_dGamma_quadForm` {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ} (hgap : IsPosCol (shiftCol col mu)) (u : FockAlg) : mu * numberQuad u ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.FockFieldPerturbation.number_le_dGamma_quadForm`.

-- Generated from ChapterFockFieldPerturbation.lean — theorem BookProof.FockFieldPerturbation.number_le_dGamma_quadForm
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

theorem BookProof.FockFieldPerturbation.number_le_dGamma_quadForm {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ}
    (hgap : IsPosCol (shiftCol col mu)) (u : FockAlg) :
    mu * numberQuad u ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re := by sorry
