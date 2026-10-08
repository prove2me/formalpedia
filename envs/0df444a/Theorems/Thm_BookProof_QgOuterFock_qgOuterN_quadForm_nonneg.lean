-- Prove2me | Theorems.Thm_BookProof_QgOuterFock_qgOuterN_quadForm_nonneg
-- name    : BookProof.QgOuterFock.qgOuterN_quadForm_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T17:48:19.035163+00:00
-- url     : https://prove2.me/theorems/d7d7eaf4-d8ad-4725-b7c5-42e4c412d8c7
-- title:
--   The Lean 4 theorem `qgOuterN_quadForm_nonneg` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgOuterN_quadForm_nonneg` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockEsa.lean

-- Generated from ChapterQgOuterFockEsa.lean — theorem BookProof.QgOuterFock.qgOuterN_quadForm_nonneg
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
open BookProof.HermiteProductCore
open BookProof.QgHermiteOscillator
open BookProof.QgOuterFockFL
open BookProof.QgOuterFock

variable {D : ℕ}



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

theorem BookProof.QgOuterFock.qgOuterN_quadForm_nonneg (x : qgOuterCore) : 0 ≤ quadForm qgOuterN x := by sorry
