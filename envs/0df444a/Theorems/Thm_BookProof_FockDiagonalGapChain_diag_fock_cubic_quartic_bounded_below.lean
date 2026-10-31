-- Prove2me | Theorems.Thm_BookProof_FockDiagonalGapChain_diag_fock_cubic_quartic_bounded_below
-- name    : BookProof.FockDiagonalGapChain.diag_fock_cubic_quartic_bounded_below
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T22:43:06.74243+00:00
-- url     : https://prove2.me/theorems/e9398100-4587-4ed5-8ef3-35430c75e84a
-- title:
--   `BookProof.FockDiagonalGapChain.diag_fock_cubic_quartic_bounded_below` (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) {m : ℝ} (hm : 0 < m) (hw : ∀ k, m ≤ w k) (S : Finset ℕ) (lam : ℝ) (u : F
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockDiagonalGapChain`.
--
--   `BookProof.FockDiagonalGapChain.diag_fock_cubic_quartic_bounded_below` (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) {m : ℝ} (hm : 0 < m) (hw : ∀ k, m ≤ w k) (S : Finset ℕ) (lam : ℝ) (u : FockAlg) : -(S.card * (2 * lam ^ 2 + (2 * lam ^ 2 + 1 / 2 - m) ^ 2 / 2)) * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol b (diagOnePart b w)) u)) : ℂ).re + ∑ k ∈ S, (lam * (inner ℂ (toLp u) (toLp (cubeA k u)) : ℂ).re + (inner ℂ (toLp u) (toLp (quartA k u)) : ℂ).re)
--
--   Formalization note: Lean 4 identifier `BookProof.FockDiagonalGapChain.diag_fock_cubic_quartic_bounded_below`.

-- Generated from ChapterFockDiagonalGapChain.lean — theorem BookProof.FockDiagonalGapChain.diag_fock_cubic_quartic_bounded_below
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

theorem BookProof.FockDiagonalGapChain.diag_fock_cubic_quartic_bounded_below (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) {m : ℝ}
    (hm : 0 < m) (hw : ∀ k, m ≤ w k) (S : Finset ℕ) (lam : ℝ) (u : FockAlg) :
    -(S.card * (2 * lam ^ 2 + (2 * lam ^ 2 + 1 / 2 - m) ^ 2 / 2)) * ‖toLp u‖ ^ 2
      ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol b (diagOnePart b w)) u)) : ℂ).re
        + ∑ k ∈ S, (lam * (inner ℂ (toLp u) (toLp (cubeA k u)) : ℂ).re
            + (inner ℂ (toLp u) (toLp (quartA k u)) : ℂ).re) := by sorry
