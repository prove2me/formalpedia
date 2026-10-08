-- Prove2me | Theorems.Thm_BookProof_QgOuterFock_qgSectorPoly_eq_sum_particles
-- name    : BookProof.QgOuterFock.qgSectorPoly_eq_sum_particles
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-05T18:29:48.484518+00:00
-- url     : https://prove2.me/theorems/987d36d3-0fd8-44a4-beb3-577b57b8cd1b
-- title:
--   The Lean 4 theorem `qgSectorPoly_eq_sum_particles` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgSectorPoly_eq_sum_particles` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockEsa.lean

-- Generated from ChapterQgOuterFockEsa.lean — theorem BookProof.QgOuterFock.qgSectorPoly_eq_sum_particles
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.ChapterF7
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.Qg3DGaugeEsa
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

theorem BookProof.QgOuterFock.qgSectorPoly_eq_sum_particles (n : ℕ) :
    sqSumPoly (qgKappaN n) (qgTorsionVecN n)
      = ((1 / 2 : ℝ) : ℂ) • ∑ p : Fin n,
          ((∑ j : Fin 84, ((qgKappa j : ℝ) : ℂ) •
              (YangMillsHermite.momOp (pcoord p j)).comp (YangMillsHermite.momOp (pcoord p j)))
            + ∑ m : Fin 64, (YangMillsHermite.mulOp (qgTorsionBlock p m)).comp
                (YangMillsHermite.mulOp (qgTorsionBlock p m))) := by sorry
