-- Prove2me | Theorems.Thm_BookProof_QgOuterFock_triple_swap_prime
-- name    : BookProof.QgOuterFock.triple_swap_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T17:07:56.17837+00:00
-- url     : https://prove2.me/theorems/76829f90-34b3-4ff2-a4dd-cade3c4e74eb
-- title:
--   The Lean 4 theorem `triple_swap_prime` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `triple_swap'` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockEsa.lean

-- Generated from ChapterQgOuterFockEsa.lean — theorem BookProof.QgOuterFock.triple_swap'
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.QgOuterFock

variable {D : ℕ}



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

theorem BookProof.QgOuterFock.triple_swap_prime {R : Type*} [Fintype R] {α : Type*} [AddCommMonoid α]
    (F : R → Fin D → Fin D → α) :
    ∑ i : Fin D, ∑ j : Fin D, ∑ r : R, F r i j
      = ∑ r : R, ∑ i : Fin D, ∑ j : Fin D, F r i j := by sorry
