-- Prove2me | Theorems.Thm_BookProof_QgOuterFock_qgSectorHam_essentiallySelfAdjointOn
-- name    : BookProof.QgOuterFock.qgSectorHam_essentiallySelfAdjointOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T20:35:16.077156+00:00
-- url     : https://prove2.me/theorems/484d65ab-316c-41c9-b96d-2bf8bcc29fd9
-- title:
--   The Lean 4 theorem `qgSectorHam_essentiallySelfAdjointOn` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgSectorHam_essentiallySelfAdjointOn` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockEsa.lean

-- Generated from ChapterQgOuterFockEsa.lean — theorem BookProof.QgOuterFock.qgSectorHam_essentiallySelfAdjointOn
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
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

variable {D : ℕ}

theorem BookProof.QgOuterFock.qgSectorHam_essentiallySelfAdjointOn (n : ℕ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := n * 84)) (qgSectorHam n) := by sorry
