-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFullFL_qgOuterFock_esa_farisLavine_full
-- name    : BookProof.QgOuterFockFullFL.qgOuterFock_esa_farisLavine_full
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T20:25:25.092432+00:00
-- url     : https://prove2.me/theorems/858f6ef9-d631-41cb-8164-fbc28d75ffa8
-- title:
--   `BookProof.QgOuterFockFullFL.qgOuterFock_esa_farisLavine_full` : EssentiallySelfAdjointOn qgOuterFriedDom (dsFibOp (fun n : ℕ => harmFried (n * 84)) qgSectorExt qgFLK qgSectorExt_r
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockFullFL`.
--
--   `BookProof.QgOuterFockFullFL.qgOuterFock_esa_farisLavine_full` : EssentiallySelfAdjointOn qgOuterFriedDom (dsFibOp (fun n : ℕ => harmFried (n * 84)) qgSectorExt qgFLK qgSectorExt_rel) ∧ ∀ x : qgOuterCore, ∃ h : (x : qgOuterFock) ∈ qgOuterFriedDom, dsFibOp (fun n : ℕ => harmFried (n * 84)) qgSectorExt qgFLK qgSectorExt_rel ⟨(x : qgOuterFock), h⟩ = qgOuterHam x
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockFullFL.qgOuterFock_esa_farisLavine_full`.

-- Generated from ChapterQgOuterFockFullFL.lean — theorem BookProof.QgOuterFockFullFL.qgOuterFock_esa_farisLavine_full
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Theorems.Thm_BookProof_QgOuterFockFullFL_qgSectorExt_rel
import Mathlib
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
open BookProof.HermiteProductCore
open BookProof.QgOuterFock
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

theorem BookProof.QgOuterFockFullFL.qgOuterFock_esa_farisLavine_full :
    EssentiallySelfAdjointOn qgOuterFriedDom
        (dsFibOp (fun n : ℕ => harmFried (n * 84)) qgSectorExt qgFLK qgSectorExt_rel) ∧
      ∀ x : qgOuterCore, ∃ h : (x : BookProof.QgOuterFockFL.qgOuterFock) ∈ qgOuterFriedDom,
        dsFibOp (fun n : ℕ => harmFried (n * 84)) qgSectorExt qgFLK qgSectorExt_rel
            ⟨(x : BookProof.QgOuterFockFL.qgOuterFock), h⟩ = qgOuterHam x := by sorry
