-- Prove2me | Theorems.Thm_BookProof_FockDiagonalGapChain_diag_fock_gap_of_field_perturbation
-- name    : BookProof.FockDiagonalGapChain.diag_fock_gap_of_field_perturbation
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T22:43:04.350292+00:00
-- url     : https://prove2.me/theorems/2f91bacc-f2e7-4ec4-bc5b-8811655d7513
-- title:
--   `BookProof.FockDiagonalGapChain.diag_fock_gap_of_field_perturbation` (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) {m : ℝ} (hm : 0 < m) (hw : ∀ k, m ≤ w k) {f : ℕ →₀ ℂ} (hf : 2 *...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockDiagonalGapChain`.
--
--   `BookProof.FockDiagonalGapChain.diag_fock_gap_of_field_perturbation` (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) {m : ℝ} (hm : 0 < m) (hw : ∀ k, m ≤ w k) {f : ℕ →₀ ℂ} (hf : 2 * l2norm f < m) {u : FockAlg} (h0 : u 0 = 0) : 0 < m - 2 * l2norm f ∧ (m - 2 * l2norm f) * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol b (diagOnePart b w)) u)) : ℂ).re + (inner ℂ (toLp u) (toLp (fieldVec f u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.FockDiagonalGapChain.diag_fock_gap_of_field_perturbation`.

-- Generated from ChapterFockDiagonalGapChain.lean — theorem BookProof.FockDiagonalGapChain.diag_fock_gap_of_field_perturbation
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockCubicQuarticStability
import Definitions.Def_ChapterFockCubicUnbounded
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterScalaronFockGapChain
import Mathlib
import Definitions.Def_ChapterFockDiagonalGapChain
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockCubicQuarticStability
import Definitions.Def_ChapterTruncationGapLift
open BookProof.FockSecondQuantization


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockCubicQuarticStability BookProof.FockCubicUnbounded
open BookProof.FockInteractionStability
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HermiteGalerkin
open BookProof.HermiteCore
open Module


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.FockDiagonalGapChain.diag_fock_gap_of_field_perturbation (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) {m : ℝ}
    (hm : 0 < m) (hw : ∀ k, m ≤ w k) {f : ℕ →₀ ℂ} (hf : 2 * l2norm f < m)
    {u : FockAlg} (h0 : u 0 = 0) :
    0 < m - 2 * l2norm f ∧
      (m - 2 * l2norm f) * ‖toLp u‖ ^ 2
        ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol b (diagOnePart b w)) u)) : ℂ).re
          + (inner ℂ (toLp u) (toLp (fieldVec f u)) : ℂ).re := by sorry
