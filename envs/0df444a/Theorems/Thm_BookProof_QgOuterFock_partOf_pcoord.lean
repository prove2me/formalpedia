-- Prove2me | Theorems.Thm_BookProof_QgOuterFock_partOf_pcoord
-- name    : BookProof.QgOuterFock.partOf_pcoord
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-22T03:45:59.882265+00:00
-- url     : https://prove2.me/theorems/7e8f00ee-be73-4980-9105-56dd5c8eeba7
-- title:
--   The Lean 4 theorem `partOf_pcoord` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `partOf_pcoord` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockEsa.lean

-- Generated from ChapterQgOuterFockEsa.lean — theorem BookProof.QgOuterFock.partOf_pcoord
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

theorem BookProof.QgOuterFock.partOf_pcoord {n : ℕ} (p : Fin n) (i : Fin 84) : partOf (pcoord p i) = p := by sorry
