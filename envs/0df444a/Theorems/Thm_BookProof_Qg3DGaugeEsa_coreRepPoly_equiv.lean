-- Prove2me | Theorems.Thm_BookProof_Qg3DGaugeEsa_coreRepPoly_equiv
-- name    : BookProof.Qg3DGaugeEsa.coreRepPoly_equiv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T15:07:56.528015+00:00
-- url     : https://prove2.me/theorems/2165cdfe-3ea5-4841-ad3b-b9edac1e8ee5
-- title:
--   The Lean 4 theorem `coreRepPoly_equiv` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `coreRepPoly_equiv` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQg3DGaugeEsa.lean

-- Generated from ChapterQg3DGaugeEsa.lean — theorem BookProof.Qg3DGaugeEsa.coreRepPoly_equiv
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

theorem BookProof.Qg3DGaugeEsa.coreRepPoly_equiv (p : MvPolynomial (Fin 84) ℂ) :
    (coreRepPoly 84).equiv p = coreEquiv p := by sorry
