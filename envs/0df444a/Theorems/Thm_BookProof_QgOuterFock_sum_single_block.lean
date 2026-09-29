-- Prove2me | Theorems.Thm_BookProof_QgOuterFock_sum_single_block
-- name    : BookProof.QgOuterFock.sum_single_block
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-22T03:46:21.368644+00:00
-- url     : https://prove2.me/theorems/c32ed156-a809-4d39-bd3c-f1eb69db21d0
-- title:
--   The Lean 4 theorem `sum_single_block` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sum_single_block` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockEsa.lean

-- Generated from ChapterQgOuterFockEsa.lean — theorem BookProof.QgOuterFock.sum_single_block
import Mathlib
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.QgOuterFock



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.QuantumGravity3DGauge
open BookProof.Qg3DGaugeEsa
open BookProof.QgHermiteOscillator
open BookProof.DirectSumEsa
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

theorem BookProof.QgOuterFock.sum_single_block {n : ℕ} (p : Fin n) (c : Fin 84) :
    ∑ i : Fin 84, ((if i = c then (1 : ℝ) else 0 : ℝ) : ℂ)
        • (X (pcoord p i) : MvPolynomial (Fin (n * 84)) ℂ) = X (pcoord p c) := by sorry
