-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFullFL_qgSectorData_commForm_le
-- name    : BookProof.QgOuterFockFullFL.qgSectorData_commForm_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T13:54:41.830418+00:00
-- url     : https://prove2.me/theorems/820fa608-8ae0-464a-a606-647a080bf0d1
-- title:
--   `BookProof.QgOuterFockFullFL.qgSectorData_commForm_le` (n : ℕ) (p : (qgSectorData n).C₀) : |commForm (qgSectorData n).H₀ (qgSectorData n).coreN p| ≤ qgFLc * quadForm (qgSectorData
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockFullFL`.
--
--   `BookProof.QgOuterFockFullFL.qgSectorData_commForm_le` (n : ℕ) (p : (qgSectorData n).C₀) : |commForm (qgSectorData n).H₀ (qgSectorData n).coreN p| ≤ qgFLc * quadForm (qgSectorData n).coreN p
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockFullFL.qgSectorData_commForm_le`.

-- Generated from ChapterQgOuterFockFullFL.lean — theorem BookProof.QgOuterFockFullFL.qgSectorData_commForm_le
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Mathlib
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.HermiteProductCore
open BookProof.QgHermiteOscillator
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData
open BookProof.QgOuterFock
open BookProof.QgOuterFockFullFL



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.Qg3DGaugeEsa BookProof.QuantumGravity3DGauge
open BookProof.GaussCoreQuadBounds BookProof.SqSumFarisLavine
open Filter Topology

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.QgOuterFockFullFL.qgSectorData_commForm_le (n : ℕ) (p : (qgSectorData n).C₀) :
    |commForm (qgSectorData n).H₀ (qgSectorData n).coreN p|
      ≤ qgFLc * quadForm (qgSectorData n).coreN p := by sorry
