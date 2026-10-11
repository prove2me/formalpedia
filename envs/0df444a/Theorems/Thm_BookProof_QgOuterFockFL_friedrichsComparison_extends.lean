-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFL_friedrichsComparison_extends
-- name    : BookProof.QgOuterFockFL.friedrichsComparison_extends
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T13:07:14.705189+00:00
-- url     : https://prove2.me/theorems/f7768a99-f43a-4f78-bdae-8dff1776b985
-- title:
--   `BookProof.QgOuterFockFL.friedrichsComparison_extends` [CompleteSpace F] (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) (x : P.dom) : ∃ h : (x : F) ∈ (friedrichsComparison P hde
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockFarisLavine`.
--
--   `BookProof.QgOuterFockFL.friedrichsComparison_extends` [CompleteSpace F] (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) (x : P.dom) : ∃ h : (x : F) ∈ (friedrichsComparison P hdense).dom, (friedrichsComparison P hdense).op ⟨(x : F), h⟩ = P.op x
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockFL.friedrichsComparison_extends`.

-- Generated from ChapterQgOuterFockFarisLavine.lean — theorem BookProof.QgOuterFockFL.friedrichsComparison_extends
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterHermiteProductCore
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHashimotoShiftInvert
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
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

theorem BookProof.QgOuterFockFL.friedrichsComparison_extends [CompleteSpace F] (P : PosSymOp F)
    (hdense : Dense (P.dom : Set F)) (x : P.dom) :
    ∃ h : (x : F) ∈ (friedrichsComparison P hdense).dom,
      (friedrichsComparison P hdense).op ⟨(x : F), h⟩ = P.op x := by sorry
