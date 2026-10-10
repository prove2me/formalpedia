-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFL_Comparison_essentiallySelfAdjointOn
-- name    : BookProof.QgOuterFockFL.Comparison.essentiallySelfAdjointOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T20:15:11.746539+00:00
-- url     : https://prove2.me/theorems/a175a245-568f-4c96-9567-18c3ead74594
-- title:
--   `BookProof.QgOuterFockFL.Comparison.essentiallySelfAdjointOn` [CompleteSpace F] (C : Comparison F) (H : C.dom →ₗ[ℂ] F) (hH : SymmetricOn C.dom H) (c : ℝ) (hc : 0 ≤ c) (hcomm : ∀ x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockFarisLavine`.
--
--   `BookProof.QgOuterFockFL.Comparison.essentiallySelfAdjointOn` [CompleteSpace F] (C : Comparison F) (H : C.dom →ₗ[ℂ] F) (hH : SymmetricOn C.dom H) (c : ℝ) (hc : 0 ≤ c) (hcomm : ∀ x : C.dom, |commForm H C.op x| ≤ c * quadForm C.op x) : EssentiallySelfAdjointOn C.dom H
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockFL.Comparison.essentiallySelfAdjointOn`.

-- Generated from ChapterQgOuterFockFarisLavine.lean — theorem BookProof.QgOuterFockFL.Comparison.essentiallySelfAdjointOn
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
import Definitions.Def_ChapterNavierStokesCanonicalVector
open BookProof.NavierStokesFlow.CanonicalVector
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

theorem BookProof.QgOuterFockFL.Comparison.essentiallySelfAdjointOn [CompleteSpace F] (C : Comparison F)
    (H : C.dom →ₗ[ℂ] F) (hH : SymmetricOn C.dom H) (c : ℝ) (hc : 0 ≤ c)
    (hcomm : ∀ x : C.dom, |commForm H C.op x| ≤ c * quadForm C.op x) :
    EssentiallySelfAdjointOn C.dom H := by sorry
