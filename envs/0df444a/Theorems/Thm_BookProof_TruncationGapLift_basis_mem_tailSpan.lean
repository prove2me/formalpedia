-- Prove2me | Theorems.Thm_BookProof_TruncationGapLift_basis_mem_tailSpan
-- name    : BookProof.TruncationGapLift.basis_mem_tailSpan
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:03:57.512074+00:00
-- url     : https://prove2.me/theorems/be9471d0-b67b-4476-b700-c985deea08af
-- title:
--   `BookProof.TruncationGapLift.basis_mem_tailSpan` (b : HilbertBasis ℕ ℂ F) {i m : ℕ} (him : m ≤ i) : b i ∈ tailSpan b m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTruncationGapLift`.
--
--   `BookProof.TruncationGapLift.basis_mem_tailSpan` (b : HilbertBasis ℕ ℂ F) {i m : ℕ} (him : m ≤ i) : b i ∈ tailSpan b m
--
--   Formalization note: Lean 4 identifier `BookProof.TruncationGapLift.basis_mem_tailSpan`.

-- Generated from ChapterTruncationGapLift.lean — theorem BookProof.TruncationGapLift.basis_mem_tailSpan
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
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
open BookProof.TruncationGapLift


noncomputable section


open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.BandEnclosure
open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs BookProof.YangMillsFockGapChain

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.TruncationGapLift.basis_mem_tailSpan (b : HilbertBasis ℕ ℂ F) {i m : ℕ} (him : m ≤ i) :
    b i ∈ tailSpan b m := by sorry
