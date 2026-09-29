-- Prove2me | Theorems.Thm_BookProof_QgOuterFock_pcoord_partOf_modeOf
-- name    : BookProof.QgOuterFock.pcoord_partOf_modeOf
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-22T03:46:33.95532+00:00
-- url     : https://prove2.me/theorems/a548ce24-1c83-400c-ba78-51ed7ae452fb
-- title:
--   The Lean 4 theorem `pcoord_partOf_modeOf` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pcoord_partOf_modeOf` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockEsa.lean

-- Generated from ChapterQgOuterFockEsa.lean — theorem BookProof.QgOuterFock.pcoord_partOf_modeOf
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

theorem BookProof.QgOuterFock.pcoord_partOf_modeOf {n : ℕ} (I : Fin (n * 84)) :
    pcoord (partOf I) (modeOf I) = I := by sorry
