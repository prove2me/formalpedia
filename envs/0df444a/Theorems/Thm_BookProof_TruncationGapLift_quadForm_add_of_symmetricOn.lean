-- Prove2me | Theorems.Thm_BookProof_TruncationGapLift_quadForm_add_of_symmetricOn
-- name    : BookProof.TruncationGapLift.quadForm_add_of_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:04:28.446975+00:00
-- url     : https://prove2.me/theorems/18a5805b-ce8d-405e-8b2f-c4e3457ae5ee
-- title:
--   `BookProof.TruncationGapLift.quadForm_add_of_symmetricOn` (H : D →ₗ[ℂ] F) (hsym : SymmetricOn D H) (x w : D) : quadForm H (x + w) = quadForm H x + quadForm H w + 2 * (inner ℂ (x :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTruncationGapLift`.
--
--   `BookProof.TruncationGapLift.quadForm_add_of_symmetricOn` (H : D →ₗ[ℂ] F) (hsym : SymmetricOn D H) (x w : D) : quadForm H (x + w) = quadForm H x + quadForm H w + 2 * (inner ℂ (x : F) (H w) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.TruncationGapLift.quadForm_add_of_symmetricOn`.

-- Generated from ChapterTruncationGapLift.lean — theorem BookProof.TruncationGapLift.quadForm_add_of_symmetricOn
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
import Definitions.Def_ChapterFarisLavineCore
open BookProof.TruncationGapLift


noncomputable section


open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.BandEnclosure
open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs BookProof.YangMillsFockGapChain

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {D : Submodule ℂ F}

theorem BookProof.TruncationGapLift.quadForm_add_of_symmetricOn (H : D →ₗ[ℂ] F) (hsym : SymmetricOn D H) (x w : D) :
    quadForm H (x + w) = quadForm H x + quadForm H w
      + 2 * (inner ℂ (x : F) (H w) : ℂ).re := by sorry
