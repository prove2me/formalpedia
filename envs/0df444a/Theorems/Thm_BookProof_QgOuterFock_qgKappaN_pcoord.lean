-- Prove2me | Theorems.Thm_BookProof_QgOuterFock_qgKappaN_pcoord
-- name    : BookProof.QgOuterFock.qgKappaN_pcoord
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T17:48:38.728402+00:00
-- url     : https://prove2.me/theorems/c0b87650-3643-468e-b795-1cc09c58b702
-- title:
--   The Lean 4 theorem `qgKappaN_pcoord` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgKappaN_pcoord` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockEsa.lean

-- Generated from ChapterQgOuterFockEsa.lean — theorem BookProof.QgOuterFock.qgKappaN_pcoord
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge
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

theorem BookProof.QgOuterFock.qgKappaN_pcoord {n : ℕ} (p : Fin n) (i : Fin 84) :
    qgKappaN n (pcoord p i) = qgKappa i := by sorry
