-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFullFL_qgSectorHam_commForm_le
-- name    : BookProof.QgOuterFockFullFL.qgSectorHam_commForm_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T14:12:28.032357+00:00
-- url     : https://prove2.me/theorems/989466bf-55e5-41b0-bcd0-c699a65db481
-- title:
--   `BookProof.QgOuterFockFullFL.qgSectorHam_commForm_le` (n : ℕ) (u : polyGaussCore (d := n * 84)) : |commForm (qgSectorHam n) harmCore u| ≤ qgFLc * quadForm harmCore u
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockFullFL`.
--
--   `BookProof.QgOuterFockFullFL.qgSectorHam_commForm_le` (n : ℕ) (u : polyGaussCore (d := n * 84)) : |commForm (qgSectorHam n) harmCore u| ≤ qgFLc * quadForm harmCore u
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockFullFL.qgSectorHam_commForm_le`.

-- Generated from ChapterQgOuterFockFullFL.lean — theorem BookProof.QgOuterFockFullFL.qgSectorHam_commForm_le
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Mathlib
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.HermiteProductCore
open BookProof.QgHermiteOscillator
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

theorem BookProof.QgOuterFockFullFL.qgSectorHam_commForm_le (n : ℕ) (u : polyGaussCore (d := n * 84)) :
    |commForm (qgSectorHam n) BookProof.QgOuterFockFL.harmCore u| ≤ qgFLc * quadForm BookProof.QgOuterFockFL.harmCore u := by sorry
