-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFL_Comparison_isPositiveSelfAdjointExtension
-- name    : BookProof.QgOuterFockFL.Comparison.isPositiveSelfAdjointExtension
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:20:39.505327+00:00
-- url     : https://prove2.me/theorems/d8530239-3ada-4b6e-b7d4-d03bf2ca8f20
-- title:
--   `BookProof.QgOuterFockFL.Comparison.isPositiveSelfAdjointExtension` (C : Comparison F) {D : Submodule ℂ F} (H : D →ₗ[ℂ] F) (hHD : ∀ x : D, ∃ h : (x : F) ∈ C.dom, C.op ⟨(x : F), h⟩
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockFarisLavine`.
--
--   `BookProof.QgOuterFockFL.Comparison.isPositiveSelfAdjointExtension` (C : Comparison F) {D : Submodule ℂ F} (H : D →ₗ[ℂ] F) (hHD : ∀ x : D, ∃ h : (x : F) ∈ C.dom, C.op ⟨(x : F), h⟩ = H x) : IsPositiveSelfAdjointExtension H C.op
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockFL.Comparison.isPositiveSelfAdjointExtension`.

-- Generated from ChapterQgOuterFockFarisLavine.lean — theorem BookProof.QgOuterFockFL.Comparison.isPositiveSelfAdjointExtension
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterHermiteProductCore
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.NavierStokesFlow.CanonicalVector
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup
open BookProof.YangMillsFriedrichs
open BookProof.QgOuterFockFL


open scoped ENNReal


open BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock
open BookProof.YangMillsFriedrichs
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.HashimotoShiftInvert
open BookProof.QgHermiteOscillator
open BookProof.HermiteProductCore

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.QgOuterFockFL.Comparison.isPositiveSelfAdjointExtension (C : Comparison F) {D : Submodule ℂ F}
    (H : D →ₗ[ℂ] F) (hHD : ∀ x : D, ∃ h : (x : F) ∈ C.dom, C.op ⟨(x : F), h⟩ = H x) :
    IsPositiveSelfAdjointExtension H C.op := by sorry
