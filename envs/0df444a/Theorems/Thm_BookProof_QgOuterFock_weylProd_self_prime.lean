-- Prove2me | Theorems.Thm_BookProof_QgOuterFock_weylProd_self_prime
-- name    : BookProof.QgOuterFock.weylProd_self_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T17:09:39.531185+00:00
-- url     : https://prove2.me/theorems/5a568a61-f7bc-46b8-9247-3277c4745e2a
-- title:
--   The Lean 4 theorem `weylProd_self_prime` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `weylProd_self'` in the `ChapterQgOuterFockEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockEsa.lean

-- Generated from ChapterQgOuterFockEsa.lean — theorem BookProof.QgOuterFock.weylProd_self'
import Definitions.Def_ChapterHermiteProductCore
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
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite
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

theorem BookProof.QgOuterFock.weylProd_self_prime (S : MvPolynomial (Fin D) ℂ →ₗ[ℂ] MvPolynomial (Fin D) ℂ)
    (p : MvPolynomial (Fin D) ℂ) : weylProd S S p = S (S p) := by sorry
