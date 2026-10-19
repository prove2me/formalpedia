-- Prove2me | Theorems.Thm_BookProof_TruncationGapLift_exists_galerkin_tail_decomp
-- name    : BookProof.TruncationGapLift.exists_galerkin_tail_decomp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:04:31.774988+00:00
-- url     : https://prove2.me/theorems/9c1f868f-3fc9-409f-82c4-443e014d34f6
-- title:
--   `BookProof.TruncationGapLift.exists_galerkin_tail_decomp` (b : HilbertBasis ℕ ℂ F) (m : ℕ) {v : F} (hv : v ∈ finiteModeDomain b) : ∃ x ∈ galerkinSpan b m, ∃ w ∈ tailSpan b m, v = x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTruncationGapLift`.
--
--   `BookProof.TruncationGapLift.exists_galerkin_tail_decomp` (b : HilbertBasis ℕ ℂ F) (m : ℕ) {v : F} (hv : v ∈ finiteModeDomain b) : ∃ x ∈ galerkinSpan b m, ∃ w ∈ tailSpan b m, v = x + w
--
--   Formalization note: Lean 4 identifier `BookProof.TruncationGapLift.exists_galerkin_tail_decomp`.

-- Generated from ChapterTruncationGapLift.lean — theorem BookProof.TruncationGapLift.exists_galerkin_tail_decomp
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

theorem BookProof.TruncationGapLift.exists_galerkin_tail_decomp (b : HilbertBasis ℕ ℂ F) (m : ℕ)
    {v : F} (hv : v ∈ finiteModeDomain b) :
    ∃ x ∈ galerkinSpan b m, ∃ w ∈ tailSpan b m, v = x + w := by sorry
