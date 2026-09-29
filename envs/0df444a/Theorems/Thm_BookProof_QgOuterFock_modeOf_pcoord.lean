-- Prove2me | Theorems.Thm_BookProof_QgOuterFock_modeOf_pcoord
-- name    : BookProof.QgOuterFock.modeOf_pcoord
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-22T03:46:19.820221+00:00
-- url     : https://prove2.me/theorems/34765c60-8d6a-401a-9117-3cfd3c29d0d5
-- title:
--   The Lean 4 theorem `modeOf_pcoord` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `modeOf_pcoord` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockEsa.lean

-- Generated from ChapterQgOuterFockEsa.lean — theorem BookProof.QgOuterFock.modeOf_pcoord
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

theorem BookProof.QgOuterFock.modeOf_pcoord {n : ℕ} (p : Fin n) (i : Fin 84) : modeOf (pcoord p i) = i := by sorry
