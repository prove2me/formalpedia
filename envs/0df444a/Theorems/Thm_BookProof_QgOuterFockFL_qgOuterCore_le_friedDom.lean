-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFL_qgOuterCore_le_friedDom
-- name    : BookProof.QgOuterFockFL.qgOuterCore_le_friedDom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:46:30.510972+00:00
-- url     : https://prove2.me/theorems/440bc2b2-b366-4cc7-bb0a-2fa04b59ea21
-- title:
--   `BookProof.QgOuterFockFL.qgOuterCore_le_friedDom` : qgOuterCore ≤ qgOuterFriedDom
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockFarisLavine`.
--
--   `BookProof.QgOuterFockFL.qgOuterCore_le_friedDom` : qgOuterCore ≤ qgOuterFriedDom
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockFL.qgOuterCore_le_friedDom`.

-- Generated from ChapterQgOuterFockFarisLavine.lean — theorem BookProof.QgOuterFockFL.qgOuterCore_le_friedDom
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.DirectSumEsa
open BookProof.HermiteProductCore
open BookProof.QgHermiteOscillator
open BookProof.QgOuterFock
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

theorem BookProof.QgOuterFockFL.qgOuterCore_le_friedDom : qgOuterCore ≤ qgOuterFriedDom := by sorry
