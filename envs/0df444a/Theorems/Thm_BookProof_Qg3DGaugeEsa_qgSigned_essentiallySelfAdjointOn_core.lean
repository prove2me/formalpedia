-- Prove2me | Theorems.Thm_BookProof_Qg3DGaugeEsa_qgSigned_essentiallySelfAdjointOn_core
-- name    : BookProof.Qg3DGaugeEsa.qgSigned_essentiallySelfAdjointOn_core
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-05T19:18:47.957898+00:00
-- url     : https://prove2.me/theorems/1a53e348-e643-4128-a2b6-f6cbbc9c68c2
-- title:
--   The Lean 4 theorem `qgSigned_essentiallySelfAdjointOn_core` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgSigned_essentiallySelfAdjointOn_core` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQg3DGaugeEsa.lean

-- Generated from ChapterQg3DGaugeEsa.lean — theorem BookProof.Qg3DGaugeEsa.qgSigned_essentiallySelfAdjointOn_core
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterYangMillsHermite
open BookProof.FullQuadratic
open BookProof.HermiteProductCore
open BookProof.QuantumGravity3DGauge
open BookProof.YangMillsHermite
open BookProof.Qg3DGaugeEsa



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.QuantumGravity3DGauge
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

theorem BookProof.Qg3DGaugeEsa.qgSigned_essentiallySelfAdjointOn_core (kappa : Fin 84 → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 84))
      (signedOp kappa (qgMom (coreRepPoly 84)) (torsionOps (coreRepPoly 84))) := by sorry
