-- Prove2me | Theorems.Thm_BookProof_QgOuterFock_sqSumPoly_eq_fqPoly
-- name    : BookProof.QgOuterFock.sqSumPoly_eq_fqPoly
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-05T18:29:32.332043+00:00
-- url     : https://prove2.me/theorems/ea89948d-ed75-49a7-9f78-2fdfde05f39c
-- title:
--   The Lean 4 theorem `sqSumPoly_eq_fqPoly` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sqSumPoly_eq_fqPoly` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockEsa.lean

-- Generated from ChapterQgOuterFockEsa.lean — theorem BookProof.QgOuterFock.sqSumPoly_eq_fqPoly
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterYangMillsHermite
open BookProof.ChapterF7
open BookProof.FullQuadratic
open BookProof.HermiteRelative
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.YangMillsHermite
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

theorem BookProof.QgOuterFock.sqSumPoly_eq_fqPoly {R : Type*} [Fintype R] (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) :
    sqSumPoly kappa v = fqPoly (diagP kappa) (gramQ v) 0 0 0 := by sorry
