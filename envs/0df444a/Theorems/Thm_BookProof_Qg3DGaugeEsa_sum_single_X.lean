-- Prove2me | Theorems.Thm_BookProof_Qg3DGaugeEsa_sum_single_X
-- name    : BookProof.Qg3DGaugeEsa.sum_single_X
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T15:11:28.581216+00:00
-- url     : https://prove2.me/theorems/66513045-fe5e-4a55-a491-1b264499aee2
-- title:
--   The Lean 4 theorem `sum_single_X` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sum_single_X` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQg3DGaugeEsa.lean

-- Generated from ChapterQg3DGaugeEsa.lean — theorem BookProof.Qg3DGaugeEsa.sum_single_X
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

theorem BookProof.Qg3DGaugeEsa.sum_single_X (c : Fin 84) :
    ∑ i : Fin 84, ((if i = c then (1 : ℝ) else 0 : ℝ) : ℂ) • (X i : MvPolynomial (Fin 84) ℂ)
      = X c := by sorry
