-- Prove2me | Theorems.Thm_BookProof_TruncationGapLift_gap_of_level_gap_and_tail_decoupled
-- name    : BookProof.TruncationGapLift.gap_of_level_gap_and_tail_decoupled
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:04:54.256741+00:00
-- url     : https://prove2.me/theorems/b736e4f5-67af-463c-b598-4ba735f00e94
-- title:
--   `BookProof.TruncationGapLift.gap_of_level_gap_and_tail_decoupled` (b : HilbertBasis ℕ ℂ F) (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn _ H) {m : ℕ} {mu : ℝ} (htrunc : ∀ x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTruncationGapLift`.
--
--   `BookProof.TruncationGapLift.gap_of_level_gap_and_tail_decoupled` (b : HilbertBasis ℕ ℂ F) (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn _ H) {m : ℕ} {mu : ℝ} (htrunc : ∀ x : finiteModeDomain b, (x : F) ∈ galerkinSpan b m → mu * ‖(x : F)‖ ^ 2 ≤ quadForm H x) (htail : ∀ w : finiteModeDomain b, (w : F) ∈ tailSpan b m → mu * ‖(w : F)‖ ^ 2 ≤ quadForm H w) (hdec : ∀ x w : finiteModeDomain b, (x : F) ∈ galerkinSpan b m → (w : F) ∈ tailSpan b m → (inner ℂ (x : F) (H w) : ℂ).re = 0) (v : finiteModeDomain b) : mu * ‖(v : F)‖ ^ 2 ≤ quadForm H v
--
--   Formalization note: Lean 4 identifier `BookProof.TruncationGapLift.gap_of_level_gap_and_tail_decoupled`.

-- Generated from ChapterTruncationGapLift.lean — theorem BookProof.TruncationGapLift.gap_of_level_gap_and_tail_decoupled
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFockGapChain
import Mathlib
import Definitions.Def_ChapterTruncationGapLift
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.HermiteGalerkin
open BookProof.TruncationGapLift


noncomputable section


open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.BandEnclosure
open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs BookProof.YangMillsFockGapChain

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {D : Submodule ℂ F}

theorem BookProof.TruncationGapLift.gap_of_level_gap_and_tail_decoupled (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn _ H) {m : ℕ} {mu : ℝ}
    (htrunc : ∀ x : finiteModeDomain b, (x : F) ∈ galerkinSpan b m →
      mu * ‖(x : F)‖ ^ 2 ≤ quadForm H x)
    (htail : ∀ w : finiteModeDomain b, (w : F) ∈ tailSpan b m →
      mu * ‖(w : F)‖ ^ 2 ≤ quadForm H w)
    (hdec : ∀ x w : finiteModeDomain b, (x : F) ∈ galerkinSpan b m →
      (w : F) ∈ tailSpan b m → (inner ℂ (x : F) (H w) : ℂ).re = 0)
    (v : finiteModeDomain b) : mu * ‖(v : F)‖ ^ 2 ≤ quadForm H v := by sorry
