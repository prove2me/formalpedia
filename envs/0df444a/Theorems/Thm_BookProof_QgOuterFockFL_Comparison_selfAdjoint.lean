-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFL_Comparison_selfAdjoint
-- name    : BookProof.QgOuterFockFL.Comparison.selfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:06:19.679272+00:00
-- url     : https://prove2.me/theorems/5dea6279-7493-4a1d-ad82-45c2b11da23a
-- title:
--   `BookProof.QgOuterFockFL.Comparison.selfAdjoint` (C : Comparison F) (w u : F) (hw : ∀ v : C.dom, (inner ℂ (C.op v) w : ℂ) = inner ℂ (v : F) u) : ∃ h : w ∈ C.dom, C.op ⟨w, h⟩ = u
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockFarisLavine`.
--
--   `BookProof.QgOuterFockFL.Comparison.selfAdjoint` (C : Comparison F) (w u : F) (hw : ∀ v : C.dom, (inner ℂ (C.op v) w : ℂ) = inner ℂ (v : F) u) : ∃ h : w ∈ C.dom, C.op ⟨w, h⟩ = u
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockFL.Comparison.selfAdjoint`.

-- Generated from ChapterQgOuterFockFarisLavine.lean — theorem BookProof.QgOuterFockFL.Comparison.selfAdjoint
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

theorem BookProof.QgOuterFockFL.Comparison.selfAdjoint (C : Comparison F) (w u : F)
    (hw : ∀ v : C.dom, (inner ℂ (C.op v) w : ℂ) = inner ℂ (v : F) u) :
    ∃ h : w ∈ C.dom, C.op ⟨w, h⟩ = u := by sorry
