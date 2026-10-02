-- Prove2me | Theorems.Thm_BookProof_Qg3DGaugeEsa_weylProd_self
-- name    : BookProof.Qg3DGaugeEsa.weylProd_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T15:15:56.978029+00:00
-- url     : https://prove2.me/theorems/b95bfa6c-2fd8-4625-8180-c60e68ccc065
-- title:
--   The Lean 4 theorem `weylProd_self` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `weylProd_self` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQg3DGaugeEsa.lean

-- Generated from ChapterQg3DGaugeEsa.lean — theorem BookProof.Qg3DGaugeEsa.weylProd_self
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

theorem BookProof.Qg3DGaugeEsa.weylProd_self (S : MvPolynomial (Fin 84) ℂ →ₗ[ℂ] MvPolynomial (Fin 84) ℂ)
    (p : MvPolynomial (Fin 84) ℂ) : weylProd S S p = S (S p) := by sorry
