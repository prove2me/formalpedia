-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFullFL_qgSectorExt_commForm_le
-- name    : BookProof.QgOuterFockFullFL.qgSectorExt_commForm_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T13:54:34.694454+00:00
-- url     : https://prove2.me/theorems/f0d10fe2-9de2-46fa-a3ec-8fdbc9dc7648
-- title:
--   `BookProof.QgOuterFockFullFL.qgSectorExt_commForm_le` (n : ℕ) (u : (harmFried (n * 84)).dom) : |commForm (qgSectorExt n) (harmFried (n * 84)).op u| ≤ qgFLc * quadForm (harmFried (n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockFullFL`.
--
--   `BookProof.QgOuterFockFullFL.qgSectorExt_commForm_le` (n : ℕ) (u : (harmFried (n * 84)).dom) : |commForm (qgSectorExt n) (harmFried (n * 84)).op u| ≤ qgFLc * quadForm (harmFried (n * 84)).op u
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockFullFL.qgSectorExt_commForm_le`.

-- Generated from ChapterQgOuterFockFullFL.lean — theorem BookProof.QgOuterFockFullFL.qgSectorExt_commForm_le
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Mathlib
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockFarisLavine
open BookProof.HermiteProductCore
open BookProof.QgOuterFockFL
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

theorem BookProof.QgOuterFockFullFL.qgSectorExt_commForm_le (n : ℕ) (u : (harmFried (n * 84)).dom) :
    |commForm (qgSectorExt n) (harmFried (n * 84)).op u|
      ≤ qgFLc * quadForm (harmFried (n * 84)).op u := by sorry
