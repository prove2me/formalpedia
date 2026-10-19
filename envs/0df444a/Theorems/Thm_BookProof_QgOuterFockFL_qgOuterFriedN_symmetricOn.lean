-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFL_qgOuterFriedN_symmetricOn
-- name    : BookProof.QgOuterFockFL.qgOuterFriedN_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:45:57.992248+00:00
-- url     : https://prove2.me/theorems/936f90ed-cdcb-4bc2-8346-dd89f70470c1
-- title:
--   `BookProof.QgOuterFockFL.qgOuterFriedN_symmetricOn` : SymmetricOn qgOuterFriedDom qgOuterFriedN
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockFarisLavine`.
--
--   `BookProof.QgOuterFockFL.qgOuterFriedN_symmetricOn` : SymmetricOn qgOuterFriedDom qgOuterFriedN
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockFL.qgOuterFriedN_symmetricOn`.

-- Generated from ChapterQgOuterFockFarisLavine.lean — theorem BookProof.QgOuterFockFL.qgOuterFriedN_symmetricOn
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.HermiteProductCore
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

theorem BookProof.QgOuterFockFL.qgOuterFriedN_symmetricOn : SymmetricOn qgOuterFriedDom qgOuterFriedN := by sorry
