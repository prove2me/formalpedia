-- Prove2me | Theorems.Thm_BookProof_QgOuterFockInteractionFL_qgInt_coupling_nontrivial
-- name    : BookProof.QgOuterFockInteractionFL.qgInt_coupling_nontrivial
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:27:12.539073+00:00
-- url     : https://prove2.me/theorems/608e7a83-f5a4-40bd-ac5d-c66f32d63831
-- title:
--   `BookProof.QgOuterFockInteractionFL.qgInt_coupling_nontrivial` {lam : ℝ} (hlam : lam ≠ 0) {n : ℕ} (hn : 2 ≤ n) : ∃ (r : (Fin n × Fin 64) ⊕ (Fin n × Fin 64)) (I J : Fin (n * 84)), p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockInteractionFL`.
--
--   `BookProof.QgOuterFockInteractionFL.qgInt_coupling_nontrivial` {lam : ℝ} (hlam : lam ≠ 0) {n : ℕ} (hn : 2 ≤ n) : ∃ (r : (Fin n × Fin 64) ⊕ (Fin n × Fin 64)) (I J : Fin (n * 84)), partOf I ≠ partOf J ∧ qgIntVec lam n r I ≠ 0 ∧ qgIntVec lam n r J ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockInteractionFL.qgInt_coupling_nontrivial`.

-- Generated from ChapterQgOuterFockInteractionFL.lean — theorem BookProof.QgOuterFockInteractionFL.qgInt_coupling_nontrivial
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Mathlib
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.Qg3DGaugeEsa
open BookProof.QgOuterFock
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

theorem BookProof.QgOuterFockInteractionFL.qgInt_coupling_nontrivial {lam : ℝ} (hlam : lam ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    ∃ (r : (Fin n × Fin 64) ⊕ (Fin n × Fin 64)) (I J : Fin (n * 84)),
      partOf I ≠ partOf J ∧ qgIntVec lam n r I ≠ 0 ∧ qgIntVec lam n r J ≠ 0 := by sorry
