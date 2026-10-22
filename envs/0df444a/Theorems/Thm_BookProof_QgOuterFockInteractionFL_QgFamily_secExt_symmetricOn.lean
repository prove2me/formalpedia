-- Prove2me | Theorems.Thm_BookProof_QgOuterFockInteractionFL_QgFamily_secExt_symmetricOn
-- name    : BookProof.QgOuterFockInteractionFL.QgFamily.secExt_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:25:36.429984+00:00
-- url     : https://prove2.me/theorems/3036ba49-1f5b-45d5-8447-212108ebc6fe
-- title:
--   `BookProof.QgOuterFockInteractionFL.QgFamily.secExt_symmetricOn` (n : ℕ) : SymmetricOn (harmFried (n * 84)).dom (F.secExt n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockInteractionFL`.
--
--   `BookProof.QgOuterFockInteractionFL.QgFamily.secExt_symmetricOn` (n : ℕ) : SymmetricOn (harmFried (n * 84)).dom (F.secExt n)
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockInteractionFL.QgFamily.secExt_symmetricOn`.

-- Generated from ChapterQgOuterFockInteractionFL.lean — theorem BookProof.QgOuterFockInteractionFL.QgFamily.secExt_symmetricOn
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
import Definitions.Def_ChapterFarisLavineCore
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

theorem BookProof.QgOuterFockInteractionFL.QgFamily.secExt_symmetricOn (n : ℕ) :
    SymmetricOn (harmFried (n * 84)).dom (F.secExt n) := by sorry
