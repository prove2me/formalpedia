-- Prove2me | Theorems.Thm_BookProof_TruncationGapLift_quadForm_ge_of_le_ritzInf_on
-- name    : BookProof.TruncationGapLift.quadForm_ge_of_le_ritzInf_on
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:05:27.59804+00:00
-- url     : https://prove2.me/theorems/5ef87c68-0acd-4ffa-bfd1-c381c60eec66
-- title:
--   `BookProof.TruncationGapLift.quadForm_ge_of_le_ritzInf_on` (H : D →ₗ[ℂ] F) (hpos : ∀ x : D, 0 ≤ quadForm H x) {V : Submodule ℂ F} {mu : ℝ} (hmu : mu ≤ ritzInf H V) (x : D) (hx : (x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTruncationGapLift`.
--
--   `BookProof.TruncationGapLift.quadForm_ge_of_le_ritzInf_on` (H : D →ₗ[ℂ] F) (hpos : ∀ x : D, 0 ≤ quadForm H x) {V : Submodule ℂ F} {mu : ℝ} (hmu : mu ≤ ritzInf H V) (x : D) (hx : (x : F) ∈ V) : mu * ‖(x : F)‖ ^ 2 ≤ quadForm H x
--
--   Formalization note: Lean 4 identifier `BookProof.TruncationGapLift.quadForm_ge_of_le_ritzInf_on`.

-- Generated from ChapterTruncationGapLift.lean — theorem BookProof.TruncationGapLift.quadForm_ge_of_le_ritzInf_on
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

theorem BookProof.TruncationGapLift.quadForm_ge_of_le_ritzInf_on (H : D →ₗ[ℂ] F)
    (hpos : ∀ x : D, 0 ≤ quadForm H x) {V : Submodule ℂ F} {mu : ℝ}
    (hmu : mu ≤ ritzInf H V) (x : D) (hx : (x : F) ∈ V) :
    mu * ‖(x : F)‖ ^ 2 ≤ quadForm H x := by sorry
