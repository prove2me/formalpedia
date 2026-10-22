-- Prove2me | Theorems.Thm_BookProof_QgOuterFockInteractionFL_nextPart_ne
-- name    : BookProof.QgOuterFockInteractionFL.nextPart_ne
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:26:07.160201+00:00
-- url     : https://prove2.me/theorems/dcb80f9e-a46f-4271-882a-56eb93072b4d
-- title:
--   `BookProof.QgOuterFockInteractionFL.nextPart_ne` {n : ℕ} (hn : 2 ≤ n) (p : Fin n) (hp : p.val = 0) : nextPart p ≠ p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockInteractionFL`.
--
--   `BookProof.QgOuterFockInteractionFL.nextPart_ne` {n : ℕ} (hn : 2 ≤ n) (p : Fin n) (hp : p.val = 0) : nextPart p ≠ p
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockInteractionFL.nextPart_ne`.

-- Generated from ChapterQgOuterFockInteractionFL.lean — theorem BookProof.QgOuterFockInteractionFL.nextPart_ne
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Mathlib
import Definitions.Def_ChapterQgOuterFockInteractionFL
open BookProof.QgOuterFockInteractionFL



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockFullFL
open BookProof.Qg3DGaugeEsa BookProof.QuantumGravity3DGauge
open BookProof.GaussCoreQuadBounds BookProof.SqSumFarisLavine

noncomputable section

variable (F : QgFamily)

theorem BookProof.QgOuterFockInteractionFL.nextPart_ne {n : ℕ} (hn : 2 ≤ n) (p : Fin n) (hp : p.val = 0) : nextPart p ≠ p := by sorry
