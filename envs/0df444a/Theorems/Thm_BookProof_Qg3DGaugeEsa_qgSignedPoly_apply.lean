-- Prove2me | Theorems.Thm_BookProof_Qg3DGaugeEsa_qgSignedPoly_apply
-- name    : BookProof.Qg3DGaugeEsa.qgSignedPoly_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T15:08:06.485435+00:00
-- url     : https://prove2.me/theorems/47153312-e010-4bcd-b381-aedc9fad14cc
-- title:
--   The Lean 4 theorem `qgSignedPoly_apply` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgSignedPoly_apply` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQg3DGaugeEsa.lean

-- Generated from ChapterQg3DGaugeEsa.lean — theorem BookProof.Qg3DGaugeEsa.qgSignedPoly_apply
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

theorem BookProof.Qg3DGaugeEsa.qgSignedPoly_apply (kappa : Fin 84 → ℝ) (p : MvPolynomial (Fin 84) ℂ) :
    qgSignedPoly kappa p
      = ((1 / 2 : ℝ) : ℂ)
        • ((∑ j : Fin 84, ((kappa j : ℝ) : ℂ) • pmom j (pmom j p))
            + ∑ m : Fin 64, torsionP m * (torsionP m * p)) := by sorry
