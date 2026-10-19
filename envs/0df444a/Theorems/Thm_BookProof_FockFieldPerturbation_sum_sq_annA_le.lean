-- Prove2me | Theorems.Thm_BookProof_FockFieldPerturbation_sum_sq_annA_le
-- name    : BookProof.FockFieldPerturbation.sum_sq_annA_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:35:13.784964+00:00
-- url     : https://prove2.me/theorems/2ddfc765-eb44-4784-bc04-91c5a1bb2e00
-- title:
--   `BookProof.FockFieldPerturbation.sum_sq_annA_le` (u : FockAlg) (S : Finset ℕ) : ∑ k ∈ S, ‖toLp (annA k u)‖ ^ 2 ≤ numberQuad u
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockFieldPerturbation`.
--
--   `BookProof.FockFieldPerturbation.sum_sq_annA_le` (u : FockAlg) (S : Finset ℕ) : ∑ k ∈ S, ‖toLp (annA k u)‖ ^ 2 ≤ numberQuad u
--
--   Formalization note: Lean 4 identifier `BookProof.FockFieldPerturbation.sum_sq_annA_le`.

-- Generated from ChapterFockFieldPerturbation.lean — theorem BookProof.FockFieldPerturbation.sum_sq_annA_le
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

theorem BookProof.FockFieldPerturbation.sum_sq_annA_le (u : FockAlg) (S : Finset ℕ) :
    ∑ k ∈ S, ‖toLp (annA k u)‖ ^ 2 ≤ numberQuad u := by sorry
