-- Prove2me | Theorems.Thm_BookProof_QgOuterFockInteractionFL_QgFamily_flc_nonneg
-- name    : BookProof.QgOuterFockInteractionFL.QgFamily.flc_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:09:02.198931+00:00
-- url     : https://prove2.me/theorems/19ffbc0f-0786-430d-a0e2-33d47283a332
-- title:
--   `BookProof.QgOuterFockInteractionFL.QgFamily.flc_nonneg` : 0 ≤ F.flc
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockInteractionFL`.
--
--   `BookProof.QgOuterFockInteractionFL.QgFamily.flc_nonneg` : 0 ≤ F.flc
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockInteractionFL.QgFamily.flc_nonneg`.

-- Generated from ChapterQgOuterFockInteractionFL.lean — theorem BookProof.QgOuterFockInteractionFL.QgFamily.flc_nonneg
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Mathlib
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterMajoranaClifford
open BookProof.MajoranaClifford
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

theorem BookProof.QgOuterFockInteractionFL.QgFamily.flc_nonneg : 0 ≤ F.flc := by sorry
