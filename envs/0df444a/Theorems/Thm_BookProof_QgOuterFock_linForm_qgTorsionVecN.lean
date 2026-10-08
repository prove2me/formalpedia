-- Prove2me | Theorems.Thm_BookProof_QgOuterFock_linForm_qgTorsionVecN
-- name    : BookProof.QgOuterFock.linForm_qgTorsionVecN
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-05T17:49:12.952533+00:00
-- url     : https://prove2.me/theorems/e36f5f33-ae04-435d-9170-a57e2823d54a
-- title:
--   The Lean 4 theorem `linForm_qgTorsionVecN` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `linForm_qgTorsionVecN` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockEsa.lean

-- Generated from ChapterQgOuterFockEsa.lean — theorem BookProof.QgOuterFock.linForm_qgTorsionVecN
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQg3DGaugeEsa
open BookProof.Qg3DGaugeEsa
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

theorem BookProof.QgOuterFock.linForm_qgTorsionVecN {n : ℕ} (p : Fin n) (m : Fin 64) :
    linForm (qgTorsionVecN n (p, m))
      = X (pcoord p (torsionIdx1 m)) - X (pcoord p (torsionIdx2 m)) := by sorry
