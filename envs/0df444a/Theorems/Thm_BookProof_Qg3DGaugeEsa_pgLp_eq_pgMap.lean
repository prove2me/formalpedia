-- Prove2me | Theorems.Thm_BookProof_Qg3DGaugeEsa_pgLp_eq_pgMap
-- name    : BookProof.Qg3DGaugeEsa.pgLp_eq_pgMap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T15:08:09.608652+00:00
-- url     : https://prove2.me/theorems/79eb64e7-92f5-4b6e-8c01-03c2fdc0f7ab
-- title:
--   The Lean 4 theorem `pgLp_eq_pgMap` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pgLp_eq_pgMap` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQg3DGaugeEsa.lean

-- Generated from ChapterQg3DGaugeEsa.lean — theorem BookProof.Qg3DGaugeEsa.pgLp_eq_pgMap
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

theorem BookProof.Qg3DGaugeEsa.pgLp_eq_pgMap (p : MvPolynomial (Fin 84) ℂ) : pgLp p = pgMap (d := 84) p := by sorry
