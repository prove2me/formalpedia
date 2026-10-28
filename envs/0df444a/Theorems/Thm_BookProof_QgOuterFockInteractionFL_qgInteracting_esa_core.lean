-- Prove2me | Theorems.Thm_BookProof_QgOuterFockInteractionFL_qgInteracting_esa_core
-- name    : BookProof.QgOuterFockInteractionFL.qgInteracting_esa_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:32:00.855751+00:00
-- url     : https://prove2.me/theorems/6c97e7d3-f75a-4a10-9d15-b36c251a791c
-- title:
--   `BookProof.QgOuterFockInteractionFL.qgInteracting_esa_core` (lam : ℝ) : EssentiallySelfAdjointOn qgOuterCore (qgIntFamily lam).outerHam
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockInteractionFL`.
--
--   `BookProof.QgOuterFockInteractionFL.qgInteracting_esa_core` (lam : ℝ) : EssentiallySelfAdjointOn qgOuterCore (qgIntFamily lam).outerHam
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockInteractionFL.qgInteracting_esa_core`.

-- Generated from ChapterQgOuterFockInteractionFL.lean — theorem BookProof.QgOuterFockInteractionFL.qgInteracting_esa_core
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
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterQgOuterFockInteractionFL
open BookProof.HermiteProductCore
open BookProof.QgOuterFock
open BookProof.QgOuterFockInteractionFL



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

theorem BookProof.QgOuterFockInteractionFL.qgInteracting_esa_core (lam : ℝ) :
    EssentiallySelfAdjointOn qgOuterCore (qgIntFamily lam).outerHam := by sorry
