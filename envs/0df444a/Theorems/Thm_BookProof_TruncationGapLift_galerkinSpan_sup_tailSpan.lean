-- Prove2me | Theorems.Thm_BookProof_TruncationGapLift_galerkinSpan_sup_tailSpan
-- name    : BookProof.TruncationGapLift.galerkinSpan_sup_tailSpan
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:04:10.635819+00:00
-- url     : https://prove2.me/theorems/c5c42f33-70ba-4a73-b46e-cdfc86451a4b
-- title:
--   `BookProof.TruncationGapLift.galerkinSpan_sup_tailSpan` (b : HilbertBasis ℕ ℂ F) (m : ℕ) : galerkinSpan b m ⊔ tailSpan b m = finiteModeDomain b
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTruncationGapLift`.
--
--   `BookProof.TruncationGapLift.galerkinSpan_sup_tailSpan` (b : HilbertBasis ℕ ℂ F) (m : ℕ) : galerkinSpan b m ⊔ tailSpan b m = finiteModeDomain b
--
--   Formalization note: Lean 4 identifier `BookProof.TruncationGapLift.galerkinSpan_sup_tailSpan`.

-- Generated from ChapterTruncationGapLift.lean — theorem BookProof.TruncationGapLift.galerkinSpan_sup_tailSpan
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

theorem BookProof.TruncationGapLift.galerkinSpan_sup_tailSpan (b : HilbertBasis ℕ ℂ F) (m : ℕ) :
    galerkinSpan b m ⊔ tailSpan b m = finiteModeDomain b := by sorry
