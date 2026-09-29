-- Prove2me | Theorems.Thm_BookProof_QgOuterFock_dsOp_quadForm_nonneg
-- name    : BookProof.QgOuterFock.dsOp_quadForm_nonneg
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-09-22T03:46:14.240267+00:00
-- url     : https://prove2.me/theorems/53213109-6334-4a4b-9969-9fdd9c0ea4e3
-- title:
--   The Lean 4 theorem `dsOp_quadForm_nonneg` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `dsOp_quadForm_nonneg` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockEsa.lean

-- Generated from ChapterQgOuterFockEsa.lean — theorem BookProof.QgOuterFock.dsOp_quadForm_nonneg
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

theorem BookProof.QgOuterFock.dsOp_quadForm_nonneg {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
    [∀ i, InnerProductSpace ℂ (G i)] {D : ∀ i, Submodule ℂ (G i)} (H : ∀ i, D i →ₗ[ℂ] G i)
    (hpos : ∀ (i : ι) (u : D i), 0 ≤ quadForm (H i) u) (x : dsCore D) :
    0 ≤ quadForm (dsOp H) x := by sorry
