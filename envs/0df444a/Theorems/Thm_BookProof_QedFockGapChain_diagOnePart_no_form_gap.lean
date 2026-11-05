-- Prove2me | Theorems.Thm_BookProof_QedFockGapChain_diagOnePart_no_form_gap
-- name    : BookProof.QedFockGapChain.diagOnePart_no_form_gap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:52:05.606201+00:00
-- url     : https://prove2.me/theorems/88a790e5-1a33-4309-96b1-2ffb6a9b7038
-- title:
--   `BookProof.QedFockGapChain.diagOnePart_no_form_gap` (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) {m : ℝ} {k : ℕ} (hk : w k < m) : ∃ x : finiteModeDomain b, (x : F) ≠ 0 ∧ quadForm ((finiteM
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQedFockGapChain`.
--
--   `BookProof.QedFockGapChain.diagOnePart_no_form_gap` (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) {m : ℝ} {k : ℕ} (hk : w k < m) : ∃ x : finiteModeDomain b, (x : F) ≠ 0 ∧ quadForm ((finiteModeDomain b).subtype.comp (diagOnePart b w)) x < m * ‖(x : F)‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.QedFockGapChain.diagOnePart_no_form_gap`.

-- Generated from ChapterQedFockGapChain.lean — theorem BookProof.QedFockGapChain.diagOnePart_no_form_gap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterFockDiagonalGapChain
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQedFockGapChain
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterSirkBandLedger
import Definitions.Def_ChapterTruncationGapLift
open BookProof.HermiteGalerkin


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FarisLavine
open BookProof.HermiteGalerkin BookProof.HermiteCore
open BookProof.YangMillsFriedrichs
open MeasureTheory
open BookProof.FockDiagonalGapChain


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.QedFockGapChain.diagOnePart_no_form_gap (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) {m : ℝ} {k : ℕ}
    (hk : w k < m) :
    ∃ x : finiteModeDomain b, (x : F) ≠ 0 ∧
      quadForm ((finiteModeDomain b).subtype.comp (diagOnePart b w)) x
        < m * ‖(x : F)‖ ^ 2 := by sorry
