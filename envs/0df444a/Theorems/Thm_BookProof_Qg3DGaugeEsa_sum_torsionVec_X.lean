-- Prove2me | Theorems.Thm_BookProof_Qg3DGaugeEsa_sum_torsionVec_X
-- name    : BookProof.Qg3DGaugeEsa.sum_torsionVec_X
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T17:32:43.817261+00:00
-- url     : https://prove2.me/theorems/9ee03c10-1515-4004-bea2-d4c4423d5099
-- title:
--   The Lean 4 theorem `sum_torsionVec_X` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sum_torsionVec_X` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQg3DGaugeEsa.lean

-- Generated from ChapterQg3DGaugeEsa.lean — theorem BookProof.Qg3DGaugeEsa.sum_torsionVec_X
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterQg3DGaugeEsa
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

theorem BookProof.Qg3DGaugeEsa.sum_torsionVec_X (m : Fin 64) :
    ∑ i : Fin 84, ((torsionVec m i : ℝ) : ℂ) • (X i : MvPolynomial (Fin 84) ℂ)
      = torsionP m := by sorry
