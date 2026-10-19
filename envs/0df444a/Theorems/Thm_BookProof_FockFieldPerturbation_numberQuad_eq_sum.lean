-- Prove2me | Theorems.Thm_BookProof_FockFieldPerturbation_numberQuad_eq_sum
-- name    : BookProof.FockFieldPerturbation.numberQuad_eq_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:21:38.334792+00:00
-- url     : https://prove2.me/theorems/6bb73cac-8d8b-4012-b773-ce00f2cede11
-- title:
--   `BookProof.FockFieldPerturbation.numberQuad_eq_sum` {u : FockAlg} {K : Finset ℕ} (hK : modes u ⊆ K) : numberQuad u = ∑ k ∈ K, ‖toLp (annA k u)‖ ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockFieldPerturbation`.
--
--   `BookProof.FockFieldPerturbation.numberQuad_eq_sum` {u : FockAlg} {K : Finset ℕ} (hK : modes u ⊆ K) : numberQuad u = ∑ k ∈ K, ‖toLp (annA k u)‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.FockFieldPerturbation.numberQuad_eq_sum`.

-- Generated from ChapterFockFieldPerturbation.lean — theorem BookProof.FockFieldPerturbation.numberQuad_eq_sum
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

theorem BookProof.FockFieldPerturbation.numberQuad_eq_sum {u : FockAlg} {K : Finset ℕ} (hK : modes u ⊆ K) :
    numberQuad u = ∑ k ∈ K, ‖toLp (annA k u)‖ ^ 2 := by sorry
