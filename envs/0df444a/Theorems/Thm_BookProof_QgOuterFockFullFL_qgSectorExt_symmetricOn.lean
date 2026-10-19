-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFullFL_qgSectorExt_symmetricOn
-- name    : BookProof.QgOuterFockFullFL.qgSectorExt_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T13:53:35.995112+00:00
-- url     : https://prove2.me/theorems/46363a62-005f-49d0-ba57-e7d18c6418c1
-- title:
--   `BookProof.QgOuterFockFullFL.qgSectorExt_symmetricOn` (n : ℕ) : SymmetricOn (harmFried (n * 84)).dom (qgSectorExt n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockFullFL`.
--
--   `BookProof.QgOuterFockFullFL.qgSectorExt_symmetricOn` (n : ℕ) : SymmetricOn (harmFried (n * 84)).dom (qgSectorExt n)
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockFullFL.qgSectorExt_symmetricOn`.

-- Generated from ChapterQgOuterFockFullFL.lean — theorem BookProof.QgOuterFockFullFL.qgSectorExt_symmetricOn
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

theorem BookProof.QgOuterFockFullFL.qgSectorExt_symmetricOn (n : ℕ) :
    SymmetricOn (harmFried (n * 84)).dom (qgSectorExt n) := by sorry
