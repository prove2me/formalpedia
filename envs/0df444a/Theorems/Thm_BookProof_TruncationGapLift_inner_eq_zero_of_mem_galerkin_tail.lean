-- Prove2me | Theorems.Thm_BookProof_TruncationGapLift_inner_eq_zero_of_mem_galerkin_tail
-- name    : BookProof.TruncationGapLift.inner_eq_zero_of_mem_galerkin_tail
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:04:13.812623+00:00
-- url     : https://prove2.me/theorems/f27d30fe-3d65-4f6f-b3aa-ed3cb61275ed
-- title:
--   `BookProof.TruncationGapLift.inner_eq_zero_of_mem_galerkin_tail` (b : HilbertBasis ℕ ℂ F) {m : ℕ} {x w : F} (hx : x ∈ galerkinSpan b m) (hw : w ∈ tailSpan b m) : (inner ℂ x w : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTruncationGapLift`.
--
--   `BookProof.TruncationGapLift.inner_eq_zero_of_mem_galerkin_tail` (b : HilbertBasis ℕ ℂ F) {m : ℕ} {x w : F} (hx : x ∈ galerkinSpan b m) (hw : w ∈ tailSpan b m) : (inner ℂ x w : ℂ) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.TruncationGapLift.inner_eq_zero_of_mem_galerkin_tail`.

-- Generated from ChapterTruncationGapLift.lean — theorem BookProof.TruncationGapLift.inner_eq_zero_of_mem_galerkin_tail
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

theorem BookProof.TruncationGapLift.inner_eq_zero_of_mem_galerkin_tail (b : HilbertBasis ℕ ℂ F) {m : ℕ}
    {x w : F} (hx : x ∈ galerkinSpan b m) (hw : w ∈ tailSpan b m) :
    (inner ℂ x w : ℂ) = 0 := by sorry
