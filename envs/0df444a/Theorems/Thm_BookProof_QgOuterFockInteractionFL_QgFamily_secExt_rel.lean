-- Prove2me | Theorems.Thm_BookProof_QgOuterFockInteractionFL_QgFamily_secExt_rel
-- name    : BookProof.QgOuterFockInteractionFL.QgFamily.secExt_rel
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:25:16.692782+00:00
-- url     : https://prove2.me/theorems/43ee049a-a01c-42ec-ad79-ff41bde1c2c5
-- title:
--   `BookProof.QgOuterFockInteractionFL.QgFamily.secExt_rel` : ∀ (n : ℕ) (u : (harmFried (n * 84)).dom), ‖F.secExt n u‖ ≤ F.flK * ‖(harmFried (n * 84)).op u + (u : L2d (n * 84))‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockInteractionFL`.
--
--   `BookProof.QgOuterFockInteractionFL.QgFamily.secExt_rel` : ∀ (n : ℕ) (u : (harmFried (n * 84)).dom), ‖F.secExt n u‖ ≤ F.flK * ‖(harmFried (n * 84)).op u + (u : L2d (n * 84))‖
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockInteractionFL.QgFamily.secExt_rel`.

-- Generated from ChapterQgOuterFockInteractionFL.lean — theorem BookProof.QgOuterFockInteractionFL.QgFamily.secExt_rel
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Mathlib
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockFarisLavine
open BookProof.HermiteProductCore
open BookProof.QgOuterFockFL
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

theorem BookProof.QgOuterFockInteractionFL.QgFamily.secExt_rel : ∀ (n : ℕ) (u : (harmFried (n * 84)).dom),
    ‖F.secExt n u‖ ≤ F.flK * ‖(harmFried (n * 84)).op u + (u : L2d (n * 84))‖ := by sorry
