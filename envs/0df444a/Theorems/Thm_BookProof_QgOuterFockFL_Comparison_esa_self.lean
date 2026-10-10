-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFL_Comparison_esa_self
-- name    : BookProof.QgOuterFockFL.Comparison.esa_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:33:15.111461+00:00
-- url     : https://prove2.me/theorems/4cd659ba-bb7d-4264-ad0d-89f954f4029d
-- title:
--   `BookProof.QgOuterFockFL.Comparison.esa_self` [CompleteSpace F] (C : Comparison F) : EssentiallySelfAdjointOn C.dom C.op
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockFarisLavine`.
--
--   `BookProof.QgOuterFockFL.Comparison.esa_self` [CompleteSpace F] (C : Comparison F) : EssentiallySelfAdjointOn C.dom C.op
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockFL.Comparison.esa_self`.

-- Generated from ChapterQgOuterFockFarisLavine.lean — theorem BookProof.QgOuterFockFL.Comparison.esa_self
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterHermiteProductCore
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterFarisLavineCore
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

theorem BookProof.QgOuterFockFL.Comparison.esa_self [CompleteSpace F] (C : Comparison F) :
    EssentiallySelfAdjointOn C.dom C.op := by sorry
