-- Prove2me | Theorems.Thm_BookProof_QgOuterFock_qgOuterCore_dense
-- name    : BookProof.QgOuterFock.qgOuterCore_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-22T03:46:34.509786+00:00
-- url     : https://prove2.me/theorems/85787172-e608-41fb-9ab8-625da67987a0
-- title:
--   The Lean 4 theorem `qgOuterCore_dense` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgOuterCore_dense` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockEsa.lean

-- Generated from ChapterQgOuterFockEsa.lean — theorem BookProof.QgOuterFock.qgOuterCore_dense
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

theorem BookProof.QgOuterFock.qgOuterCore_dense : Dense ((qgOuterCore : Submodule ℂ qgOuterFock) : Set qgOuterFock) := by sorry
