-- Prove2me | Theorems.Thm_BookProof_Qg3DGaugeEsa_pgLp_qgSignedPoly
-- name    : BookProof.Qg3DGaugeEsa.pgLp_qgSignedPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T17:32:42.968211+00:00
-- url     : https://prove2.me/theorems/939344c0-157c-42cc-b7f3-47fc80f8d9b6
-- title:
--   The Lean 4 theorem `pgLp_qgSignedPoly` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pgLp_qgSignedPoly` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQg3DGaugeEsa.lean

-- Generated from ChapterQg3DGaugeEsa.lean — theorem BookProof.Qg3DGaugeEsa.pgLp_qgSignedPoly
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
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
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

theorem BookProof.Qg3DGaugeEsa.pgLp_qgSignedPoly (kappa : Fin 84 → ℝ) (p : MvPolynomial (Fin 84) ℂ) :
    pgLp (qgSignedPoly kappa p)
      = ((1 / 2 : ℝ) : ℂ)
        • ((∑ j : Fin 84, ((kappa j : ℝ) : ℂ) • pgLp (pmom j (pmom j p)))
            + ∑ m : Fin 64, pgLp (torsionP m * (torsionP m * p))) := by sorry
