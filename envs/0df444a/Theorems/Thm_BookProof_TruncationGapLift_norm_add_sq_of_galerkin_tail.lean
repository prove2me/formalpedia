-- Prove2me | Theorems.Thm_BookProof_TruncationGapLift_norm_add_sq_of_galerkin_tail
-- name    : BookProof.TruncationGapLift.norm_add_sq_of_galerkin_tail
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:04:22.354974+00:00
-- url     : https://prove2.me/theorems/cb3f79a9-52f1-4fa3-bcc4-d7de9dd23ae5
-- title:
--   `BookProof.TruncationGapLift.norm_add_sq_of_galerkin_tail` (b : HilbertBasis ℕ ℂ F) {m : ℕ} {x w : F} (hx : x ∈ galerkinSpan b m) (hw : w ∈ tailSpan b m) : ‖x + w‖ ^ 2 = ‖x‖ ^ 2 +
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTruncationGapLift`.
--
--   `BookProof.TruncationGapLift.norm_add_sq_of_galerkin_tail` (b : HilbertBasis ℕ ℂ F) {m : ℕ} {x w : F} (hx : x ∈ galerkinSpan b m) (hw : w ∈ tailSpan b m) : ‖x + w‖ ^ 2 = ‖x‖ ^ 2 + ‖w‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.TruncationGapLift.norm_add_sq_of_galerkin_tail`.

-- Generated from ChapterTruncationGapLift.lean — theorem BookProof.TruncationGapLift.norm_add_sq_of_galerkin_tail
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

theorem BookProof.TruncationGapLift.norm_add_sq_of_galerkin_tail (b : HilbertBasis ℕ ℂ F) {m : ℕ}
    {x w : F} (hx : x ∈ galerkinSpan b m) (hw : w ∈ tailSpan b m) :
    ‖x + w‖ ^ 2 = ‖x‖ ^ 2 + ‖w‖ ^ 2 := by sorry
