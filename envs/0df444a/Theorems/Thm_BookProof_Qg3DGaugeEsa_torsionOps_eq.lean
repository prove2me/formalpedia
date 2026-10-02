-- Prove2me | Theorems.Thm_BookProof_Qg3DGaugeEsa_torsionOps_eq
-- name    : BookProof.Qg3DGaugeEsa.torsionOps_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T15:12:00.476804+00:00
-- url     : https://prove2.me/theorems/03f6f850-e8ef-45fa-a07e-0b955c5bad98
-- title:
--   The Lean 4 theorem `torsionOps_eq` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `torsionOps_eq` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQg3DGaugeEsa.lean

-- Generated from ChapterQg3DGaugeEsa.lean — theorem BookProof.Qg3DGaugeEsa.torsionOps_eq
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

theorem BookProof.Qg3DGaugeEsa.torsionOps_eq {D : Submodule ℂ (L2d 84)} (Φ : CoreRep 84 D) (m : Fin 64) :
    torsionOps Φ m = Φ.op (mulOp (torsionP m)) := by sorry
