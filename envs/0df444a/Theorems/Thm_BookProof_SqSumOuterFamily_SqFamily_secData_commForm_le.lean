-- Prove2me | Theorems.Thm_BookProof_SqSumOuterFamily_SqFamily_secData_commForm_le
-- name    : BookProof.SqSumOuterFamily.SqFamily.secData_commForm_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:58:03.024379+00:00
-- url     : https://prove2.me/theorems/83aa5ad1-be96-45d7-adc1-fc0f7bc85b3c
-- title:
--   `BookProof.SqSumOuterFamily.SqFamily.secData_commForm_le` (n : ℕ) (p : (F.secData n).C₀) : |commForm (F.secData n).H₀ (F.secData n).coreN p| ≤ F.flc * quadForm (F.secData n).coreN
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSqSumOuterFamily`.
--
--   `BookProof.SqSumOuterFamily.SqFamily.secData_commForm_le` (n : ℕ) (p : (F.secData n).C₀) : |commForm (F.secData n).H₀ (F.secData n).coreN p| ≤ F.flc * quadForm (F.secData n).coreN p
--
--   Formalization note: Lean 4 identifier `BookProof.SqSumOuterFamily.SqFamily.secData_commForm_le`.

-- Generated from ChapterSqSumOuterFamily.lean — theorem BookProof.SqSumOuterFamily.SqFamily.secData_commForm_le
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Mathlib
import Definitions.Def_ChapterSqSumOuterFamily
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterLeafGaps
import Definitions.Def_ChapterQgOuterFockInteractionFL
open BookProof.HermiteProductCore
open BookProof.QgHermiteOscillator
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockFullFL
open BookProof.GaussCoreQuadBounds BookProof.SqSumFarisLavine
open BookProof.SqSumOuterFamily

noncomputable section

variable (dim : ℕ → ℕ)
variable (F : SqFamily)

theorem BookProof.SqSumOuterFamily.SqFamily.secData_commForm_le (n : ℕ) (p : (F.secData n).C₀) :
    |commForm (F.secData n).H₀ (F.secData n).coreN p|
      ≤ F.flc * quadForm (F.secData n).coreN p := by sorry
