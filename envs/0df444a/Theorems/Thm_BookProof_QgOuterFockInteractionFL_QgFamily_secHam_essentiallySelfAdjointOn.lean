-- Prove2me | Theorems.Thm_BookProof_QgOuterFockInteractionFL_QgFamily_secHam_essentiallySelfAdjointOn
-- name    : BookProof.QgOuterFockInteractionFL.QgFamily.secHam_essentiallySelfAdjointOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:25:10.973843+00:00
-- url     : https://prove2.me/theorems/82b69d66-3c66-415d-90b0-c51631de9dc1
-- title:
--   `BookProof.QgOuterFockInteractionFL.QgFamily.secHam_essentiallySelfAdjointOn` (n : ℕ) : EssentiallySelfAdjointOn (polyGaussCore (d := n * 84)) (F.secHam n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockInteractionFL`.
--
--   `BookProof.QgOuterFockInteractionFL.QgFamily.secHam_essentiallySelfAdjointOn` (n : ℕ) : EssentiallySelfAdjointOn (polyGaussCore (d := n * 84)) (F.secHam n)
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockInteractionFL.QgFamily.secHam_essentiallySelfAdjointOn`.

-- Generated from ChapterQgOuterFockInteractionFL.lean — theorem BookProof.QgOuterFockInteractionFL.QgFamily.secHam_essentiallySelfAdjointOn
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
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
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

theorem BookProof.QgOuterFockInteractionFL.QgFamily.secHam_essentiallySelfAdjointOn (n : ℕ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := n * 84)) (F.secHam n) := by sorry
