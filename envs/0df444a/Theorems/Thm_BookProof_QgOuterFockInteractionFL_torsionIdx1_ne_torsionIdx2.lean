-- Prove2me | Theorems.Thm_BookProof_QgOuterFockInteractionFL_torsionIdx1_ne_torsionIdx2
-- name    : BookProof.QgOuterFockInteractionFL.torsionIdx1_ne_torsionIdx2
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:26:51.5263+00:00
-- url     : https://prove2.me/theorems/32cdb7c1-46d4-4f32-ab88-d8934c740098
-- title:
--   `BookProof.QgOuterFockInteractionFL.torsionIdx1_ne_torsionIdx2` {m : Fin 64} (hm : torsionMu m ≠ torsionNu m) : torsionIdx1 m ≠ torsionIdx2 m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockInteractionFL`.
--
--   `BookProof.QgOuterFockInteractionFL.torsionIdx1_ne_torsionIdx2` {m : Fin 64} (hm : torsionMu m ≠ torsionNu m) : torsionIdx1 m ≠ torsionIdx2 m
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockInteractionFL.torsionIdx1_ne_torsionIdx2`.

-- Generated from ChapterQgOuterFockInteractionFL.lean — theorem BookProof.QgOuterFockInteractionFL.torsionIdx1_ne_torsionIdx2
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Mathlib
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterQg3DGaugeEsa
open BookProof.Qg3DGaugeEsa
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

theorem BookProof.QgOuterFockInteractionFL.torsionIdx1_ne_torsionIdx2 {m : Fin 64} (hm : torsionMu m ≠ torsionNu m) :
    torsionIdx1 m ≠ torsionIdx2 m := by sorry
