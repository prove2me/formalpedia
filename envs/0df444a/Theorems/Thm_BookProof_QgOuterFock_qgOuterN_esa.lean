-- Prove2me | Theorems.Thm_BookProof_QgOuterFock_qgOuterN_esa
-- name    : BookProof.QgOuterFock.qgOuterN_esa
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-09-22T03:46:50.915512+00:00
-- url     : https://prove2.me/theorems/81faee7b-9cde-4d1c-ab2c-f8745e476a35
-- title:
--   The Lean 4 theorem `qgOuterN_esa` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgOuterN_esa` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockEsa.lean

-- Generated from ChapterQgOuterFockEsa.lean — theorem BookProof.QgOuterFock.qgOuterN_esa
import Mathlib
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.QgOuterFock



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.QuantumGravity3DGauge
open BookProof.Qg3DGaugeEsa
open BookProof.QgHermiteOscillator
open BookProof.DirectSumEsa
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

theorem BookProof.QgOuterFock.qgOuterN_esa : EssentiallySelfAdjointOn qgOuterCore qgOuterN := by sorry
