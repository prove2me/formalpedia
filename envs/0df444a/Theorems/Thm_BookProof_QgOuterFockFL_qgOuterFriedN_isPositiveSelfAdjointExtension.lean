-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFL_qgOuterFriedN_isPositiveSelfAdjointExtension
-- name    : BookProof.QgOuterFockFL.qgOuterFriedN_isPositiveSelfAdjointExtension
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:47:10.399603+00:00
-- url     : https://prove2.me/theorems/dd3d36d6-7e7e-4232-b340-0009c4ddbacd
-- title:
--   `BookProof.QgOuterFockFL.qgOuterFriedN_isPositiveSelfAdjointExtension` : IsPositiveSelfAdjointExtension qgOuterN qgOuterFriedN
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockFarisLavine`.
--
--   `BookProof.QgOuterFockFL.qgOuterFriedN_isPositiveSelfAdjointExtension` : IsPositiveSelfAdjointExtension qgOuterN qgOuterFriedN
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockFL.qgOuterFriedN_isPositiveSelfAdjointExtension`.

-- Generated from ChapterQgOuterFockFarisLavine.lean — theorem BookProof.QgOuterFockFL.qgOuterFriedN_isPositiveSelfAdjointExtension
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.DirectSumEsa
open BookProof.HermiteProductCore
open BookProof.QgHermiteOscillator
open BookProof.QgOuterFock
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
variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]
variable (C : ∀ i, Comparison (G i))
variable (H : ∀ i, (C i).dom →ₗ[ℂ] G i)
variable {C H}

theorem BookProof.QgOuterFockFL.qgOuterFriedN_isPositiveSelfAdjointExtension :
    IsPositiveSelfAdjointExtension qgOuterN qgOuterFriedN := by sorry
