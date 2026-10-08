-- Prove2me | Theorems.Thm_BookProof_Qg3DGaugeEsa_qg3DElliptic_essentiallySelfAdjointOn_core
-- name    : BookProof.Qg3DGaugeEsa.qg3DElliptic_essentiallySelfAdjointOn_core
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-05T19:32:53.7789+00:00
-- url     : https://prove2.me/theorems/40b0846c-c406-4966-a309-e58924ea6fb7
-- title:
--   The Lean 4 theorem `qg3DElliptic_essentiallySelfAdjointOn_core` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qg3DElliptic_essentiallySelfAdjointOn_core` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQg3DGaugeEsa.lean

-- Generated from ChapterQg3DGaugeEsa.lean — theorem BookProof.Qg3DGaugeEsa.qg3DElliptic_essentiallySelfAdjointOn_core
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterYangMillsHermite
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

theorem BookProof.Qg3DGaugeEsa.qg3DElliptic_essentiallySelfAdjointOn_core :
    EssentiallySelfAdjointOn (polyGaussCore (d := 84))
      (qg3DEllipticHamiltonian (coreRepPoly 84)) := by sorry
