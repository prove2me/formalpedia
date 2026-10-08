-- Prove2me | Theorems.Thm_BookProof_Qg3DGaugeEsa_qgFqQ_quadratic_eq
-- name    : BookProof.Qg3DGaugeEsa.qgFqQ_quadratic_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T18:25:59.784429+00:00
-- url     : https://prove2.me/theorems/858e21dc-95a5-4b10-8dd9-3a0ea0ed6f19
-- title:
--   The Lean 4 theorem `qgFqQ_quadratic_eq` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgFqQ_quadratic_eq` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQg3DGaugeEsa.lean

-- Generated from ChapterQg3DGaugeEsa.lean — theorem BookProof.Qg3DGaugeEsa.qgFqQ_quadratic_eq
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

theorem BookProof.Qg3DGaugeEsa.qgFqQ_quadratic_eq :
    ∑ i : Fin 84, ∑ j : Fin 84, ((qgFqQ i j : ℝ) : ℂ)
        • ((X i : MvPolynomial (Fin 84) ℂ) * X j)
      = ((1 / 2 : ℝ) : ℂ) • ∑ m : Fin 64, torsionP m * torsionP m := by sorry
