-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFullFL_qgSector_gradFun_le
-- name    : BookProof.QgOuterFockFullFL.qgSector_gradFun_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T13:53:03.031251+00:00
-- url     : https://prove2.me/theorems/f56763bb-f87e-4191-b162-d4e02b1f8aec
-- title:
--   `BookProof.QgOuterFockFullFL.qgSector_gradFun_le` (n : ℕ) (x : Vd (n * 84)) : ∑ k : Fin (n * 84), (gradFun (qgTorsionVecN n) k x) ^ 2 ≤ (128 : ℝ) ^ 2 * ‖x‖ ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockFullFL`.
--
--   `BookProof.QgOuterFockFullFL.qgSector_gradFun_le` (n : ℕ) (x : Vd (n * 84)) : ∑ k : Fin (n * 84), (gradFun (qgTorsionVecN n) k x) ^ 2 ≤ (128 : ℝ) ^ 2 * ‖x‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockFullFL.qgSector_gradFun_le`.

-- Generated from ChapterQgOuterFockFullFL.lean — theorem BookProof.QgOuterFockFullFL.qgSector_gradFun_le
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterGaussCoreQuadBounds
import Mathlib
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.HermiteProductCore
open BookProof.QgOuterFock
open BookProof.SqSumFarisLavine
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

theorem BookProof.QgOuterFockFullFL.qgSector_gradFun_le (n : ℕ) (x : Vd (n * 84)) :
    ∑ k : Fin (n * 84), (gradFun (qgTorsionVecN n) k x) ^ 2 ≤ (128 : ℝ) ^ 2 * ‖x‖ ^ 2 := by sorry
