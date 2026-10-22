-- Prove2me | Theorems.Thm_BookProof_QgOuterFockInteractionFL_QgFamily_outerHam_esa
-- name    : BookProof.QgOuterFockInteractionFL.QgFamily.outerHam_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:25:09.217699+00:00
-- url     : https://prove2.me/theorems/3793d5e0-2b83-490f-8dd4-b41a7ee80367
-- title:
--   `BookProof.QgOuterFockInteractionFL.QgFamily.outerHam_esa` : EssentiallySelfAdjointOn qgOuterCore F.outerHam
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockInteractionFL`.
--
--   `BookProof.QgOuterFockInteractionFL.QgFamily.outerHam_esa` : EssentiallySelfAdjointOn qgOuterCore F.outerHam
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockInteractionFL.QgFamily.outerHam_esa`.

-- Generated from ChapterQgOuterFockInteractionFL.lean — theorem BookProof.QgOuterFockInteractionFL.QgFamily.outerHam_esa
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Mathlib
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.HermiteProductCore
open BookProof.QgOuterFock
open BookProof.QgOuterFockInteractionFL
open BookProof.QgOuterFockInteractionFL.QgFamily



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockFullFL
open BookProof.Qg3DGaugeEsa BookProof.QuantumGravity3DGauge
open BookProof.GaussCoreQuadBounds BookProof.SqSumFarisLavine

noncomputable section

variable (F : QgFamily)

theorem BookProof.QgOuterFockInteractionFL.QgFamily.outerHam_esa : EssentiallySelfAdjointOn qgOuterCore F.outerHam := by sorry
